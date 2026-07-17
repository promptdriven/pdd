/*
 * Checker-owned N-API primitive for the trusted Vitest reporter.
 *
 * This intentionally contains no JavaScript policy: the reporter supplies the
 * fixed checker descriptor and its already-measured FIFO identity, and this
 * module seals the coordinator procfs boundary and marks every same-object
 * descriptor close-on-exec before Vitest starts its worker processes.
 * FD_CLOEXEC does not close the reporter's descriptor; it only prevents future
 * fork+exec worker processes from inheriting it.
 */
#include <node_api.h>

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static napi_value pdd_error(napi_env env, const char *message) {
  napi_throw_error(env, NULL, message);
  return NULL;
}

static int pdd_set_cloexec(int descriptor) {
#ifdef PDD_TEST_FORCE_FCNTL_ERROR
  (void)descriptor;
  errno = EPERM;
  return -1;
#else
  int flags = fcntl(descriptor, F_GETFD);
  if (flags < 0) {
    return -1;
  }
  return fcntl(descriptor, F_SETFD, flags | FD_CLOEXEC);
#endif
}

static int pdd_seal_coordinator_procfs(void) {
#ifdef PDD_TEST_FORCE_PRCTL_ERROR
  errno = EPERM;
  return -1;
#else
  int dumpable;
  if (prctl(PR_SET_DUMPABLE, 0, 0, 0, 0) != 0) {
    return -1;
  }
  dumpable = prctl(PR_GET_DUMPABLE, 0, 0, 0, 0);
  if (dumpable != 0) {
    if (dumpable >= 0) {
      errno = EPERM;
    }
    return -1;
  }
  return 0;
#endif
}

static int pdd_bigint_argument(
    napi_env env, napi_value value, uint64_t *output, const char *name) {
  bool lossless = false;
  napi_status status = napi_get_value_bigint_uint64(env, value, output, &lossless);
  if (status != napi_ok || !lossless) {
    napi_throw_type_error(env, NULL, name);
    return 0;
  }
  return 1;
}

static napi_value pdd_seal_result_authority(
    napi_env env, napi_callback_info info) {
  size_t count = 3;
  napi_value arguments[3];
  int32_t result_fd = -1;
  uint64_t expected_device = 0;
  uint64_t expected_inode = 0;
  struct stat primary;
  DIR *directory = NULL;
  struct dirent *entry;
  uint32_t sealed = 0;
  int verified_flags;

  if (napi_get_cb_info(env, info, &count, arguments, NULL, NULL) != napi_ok ||
      count != 3 ||
      napi_get_value_int32(env, arguments[0], &result_fd) != napi_ok ||
      result_fd < 0 ||
      !pdd_bigint_argument(env, arguments[1], &expected_device,
                           "expected result device must be a bigint") ||
      !pdd_bigint_argument(env, arguments[2], &expected_inode,
                           "expected result inode must be a bigint")) {
    return pdd_error(env, "invalid trusted Vitest result authority arguments");
  }

  if (fstat(result_fd, &primary) != 0 || !S_ISFIFO(primary.st_mode) ||
      (uint64_t)primary.st_dev != expected_device ||
      (uint64_t)primary.st_ino != expected_inode) {
    return pdd_error(env, "trusted Vitest result descriptor identity mismatch");
  }
  if (pdd_seal_coordinator_procfs() != 0) {
    return pdd_error(env, "trusted Vitest coordinator procfs seal failed");
  }

  directory = opendir("/proc/self/fd");
  if (directory == NULL) {
    return pdd_error(env, "trusted Vitest descriptor table is unavailable");
  }
  errno = 0;
  while ((entry = readdir(directory)) != NULL) {
    char *end = NULL;
    long parsed;
    int descriptor;
    struct stat observed;
    errno = 0;
    parsed = strtol(entry->d_name, &end, 10);
    if (errno != 0 || end == entry->d_name || *end != '\0' || parsed < 0 ||
        parsed > INT32_MAX) {
      continue;
    }
    descriptor = (int)parsed;
    if (fstat(descriptor, &observed) != 0) {
      int failure = errno;
      closedir(directory);
      errno = failure;
      return pdd_error(env, "trusted Vitest descriptor inspection failed");
    }
    if (!S_ISFIFO(observed.st_mode) ||
        (uint64_t)observed.st_dev != expected_device ||
        (uint64_t)observed.st_ino != expected_inode) {
      continue;
    }
    if (pdd_set_cloexec(descriptor) != 0) {
      int failure = errno;
      closedir(directory);
      errno = failure;
      return pdd_error(env, "trusted Vitest result descriptor sealing failed");
    }
    verified_flags = fcntl(descriptor, F_GETFD);
    if (verified_flags < 0 || (verified_flags & FD_CLOEXEC) == 0) {
      closedir(directory);
      return pdd_error(env, "trusted Vitest result descriptor seal verification failed");
    }
    sealed++;
  }
  if (errno != 0) {
    int failure = errno;
    closedir(directory);
    errno = failure;
    return pdd_error(env, "trusted Vitest descriptor table read failed");
  }
  if (closedir(directory) != 0) {
    return pdd_error(env, "trusted Vitest descriptor table close failed");
  }
  if (sealed == 0) {
    return pdd_error(env, "trusted Vitest result descriptor alias was not found");
  }

  napi_value result;
  if (napi_create_uint32(env, sealed, &result) != napi_ok) {
    return pdd_error(env, "trusted Vitest result authority response failed");
  }
  return result;
}

#ifdef PDD_TEST_EXEC_PROBE
/* Compiled only by the Linux regression harness, never in the shipped addon. */
static napi_value pdd_probe_exec(napi_env env, napi_callback_info info) {
  size_t count = 3;
  napi_value arguments[3];
  size_t executable_size = 0;
  char *executable = NULL;
  int32_t first_fd = -1;
  int32_t second_fd = -1;
  pid_t child;
  int status;
  char first_text[32];
  char second_text[32];
  const char *script =
      "const fs=require('node:fs'); for (const value of process.argv.slice(1)) "
      "{ try { fs.fstatSync(Number(value)); process.exit(7); } catch (_) {} }";

  if (napi_get_cb_info(env, info, &count, arguments, NULL, NULL) != napi_ok ||
      count != 3 ||
      napi_get_value_string_utf8(env, arguments[0], NULL, 0, &executable_size) !=
          napi_ok ||
      executable_size == 0 ||
      napi_get_value_int32(env, arguments[1], &first_fd) != napi_ok ||
      napi_get_value_int32(env, arguments[2], &second_fd) != napi_ok ||
      first_fd < 0 || second_fd < 0) {
    return pdd_error(env, "invalid trusted Vitest exec probe arguments");
  }
  executable = malloc(executable_size + 1);
  if (executable == NULL ||
      napi_get_value_string_utf8(env, arguments[0], executable,
                                 executable_size + 1, &executable_size) != napi_ok) {
    free(executable);
    return pdd_error(env, "trusted Vitest exec probe allocation failed");
  }
  snprintf(first_text, sizeof(first_text), "%d", first_fd);
  snprintf(second_text, sizeof(second_text), "%d", second_fd);
  child = fork();
  if (child < 0) {
    free(executable);
    return pdd_error(env, "trusted Vitest exec probe fork failed");
  }
  if (child == 0) {
    execl(executable, executable, "-e", script, first_text, second_text, (char *)NULL);
    _exit(127);
  }
  free(executable);
  if (waitpid(child, &status, 0) != child || !WIFEXITED(status)) {
    return pdd_error(env, "trusted Vitest exec probe wait failed");
  }
  napi_value result;
  if (napi_create_int32(env, WEXITSTATUS(status), &result) != napi_ok) {
    return pdd_error(env, "trusted Vitest exec probe response failed");
  }
  return result;
}
#endif

static napi_value pdd_initialize(napi_env env, napi_value exports) {
  napi_value seal;
  if (napi_create_function(
          env, "sealResultAuthority", NAPI_AUTO_LENGTH,
          pdd_seal_result_authority, NULL, &seal) != napi_ok ||
      napi_set_named_property(env, exports, "sealResultAuthority", seal) != napi_ok) {
    return NULL;
  }
#ifdef PDD_TEST_EXEC_PROBE
  napi_value probe;
  if (napi_create_function(
          env, "probeExec", NAPI_AUTO_LENGTH, pdd_probe_exec, NULL, &probe) !=
          napi_ok ||
      napi_set_named_property(env, exports, "probeExec", probe) != napi_ok) {
    return NULL;
  }
#endif
  return exports;
}

NAPI_MODULE(NODE_GYP_MODULE_NAME, pdd_initialize)
