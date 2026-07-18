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

/*
 * Stage A transports only these fixed values.  Do not substitute errno,
 * strerror(), N-API status text, or a caller-controlled string here: the
 * reporter can authenticate an enum, but not diagnostic prose.
 */
typedef enum {
  PDD_SEAL_FAILURE_INVALID_ARGUMENT,
  PDD_SEAL_FAILURE_DESCRIPTOR_IDENTITY,
  PDD_SEAL_FAILURE_PROCFS_SEAL,
  PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_OPEN,
  PDD_SEAL_FAILURE_DESCRIPTOR_INSPECTION,
  PDD_SEAL_FAILURE_CLOEXEC_SET,
  PDD_SEAL_FAILURE_CLOEXEC_VERIFICATION,
  PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_READ,
  PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_CLOSE,
  PDD_SEAL_FAILURE_ALIAS_NOT_FOUND,
  PDD_SEAL_FAILURE_RESPONSE_CREATION,
} pdd_seal_failure_reason;

static const char *pdd_seal_failure_code(pdd_seal_failure_reason reason) {
  switch (reason) {
    case PDD_SEAL_FAILURE_INVALID_ARGUMENT:
      return "PDD_VITEST_SEAL_INVALID_ARGUMENT";
    case PDD_SEAL_FAILURE_DESCRIPTOR_IDENTITY:
      return "PDD_VITEST_SEAL_DESCRIPTOR_IDENTITY";
    case PDD_SEAL_FAILURE_PROCFS_SEAL:
      return "PDD_VITEST_SEAL_PROCFS_SEAL";
    case PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_OPEN:
      return "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_OPEN";
    case PDD_SEAL_FAILURE_DESCRIPTOR_INSPECTION:
      return "PDD_VITEST_SEAL_DESCRIPTOR_INSPECTION";
    case PDD_SEAL_FAILURE_CLOEXEC_SET:
      return "PDD_VITEST_SEAL_CLOEXEC_SET";
    case PDD_SEAL_FAILURE_CLOEXEC_VERIFICATION:
      return "PDD_VITEST_SEAL_CLOEXEC_VERIFICATION";
    case PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_READ:
      return "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_READ";
    case PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_CLOSE:
      return "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_CLOSE";
    case PDD_SEAL_FAILURE_ALIAS_NOT_FOUND:
      return "PDD_VITEST_SEAL_ALIAS_NOT_FOUND";
    case PDD_SEAL_FAILURE_RESPONSE_CREATION:
      return "PDD_VITEST_SEAL_RESPONSE_CREATION";
  }
  return "PDD_VITEST_SEAL_INVALID_ARGUMENT";
}

static napi_value pdd_seal_error(
    napi_env env, pdd_seal_failure_reason reason) {
  const char *code = pdd_seal_failure_code(reason);
  napi_throw_error(env, code, code);
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
    napi_env env, napi_value value, uint64_t *output) {
  bool lossless = false;
  napi_status status = napi_get_value_bigint_uint64(env, value, output, &lossless);
  if (status != napi_ok || !lossless) {
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

#ifdef PDD_TEST_FORCE_SEAL_FAILURE
  return pdd_seal_error(env, PDD_TEST_FORCE_SEAL_FAILURE);
#endif

  if (napi_get_cb_info(env, info, &count, arguments, NULL, NULL) != napi_ok ||
      count != 3 ||
      napi_get_value_int32(env, arguments[0], &result_fd) != napi_ok ||
      result_fd < 0 ||
      !pdd_bigint_argument(env, arguments[1], &expected_device) ||
      !pdd_bigint_argument(env, arguments[2], &expected_inode)) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_INVALID_ARGUMENT);
  }

  if (fstat(result_fd, &primary) != 0 || !S_ISFIFO(primary.st_mode) ||
      (uint64_t)primary.st_dev != expected_device ||
      (uint64_t)primary.st_ino != expected_inode) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_DESCRIPTOR_IDENTITY);
  }
  if (pdd_seal_coordinator_procfs() != 0) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_PROCFS_SEAL);
  }

  directory = opendir("/proc/self/fd");
  if (directory == NULL) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_OPEN);
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
      closedir(directory);
      return pdd_seal_error(env, PDD_SEAL_FAILURE_DESCRIPTOR_INSPECTION);
    }
    if (!S_ISFIFO(observed.st_mode) ||
        (uint64_t)observed.st_dev != expected_device ||
        (uint64_t)observed.st_ino != expected_inode) {
      continue;
    }
    if (pdd_set_cloexec(descriptor) != 0) {
      closedir(directory);
      return pdd_seal_error(env, PDD_SEAL_FAILURE_CLOEXEC_SET);
    }
    verified_flags = fcntl(descriptor, F_GETFD);
    if (verified_flags < 0 || (verified_flags & FD_CLOEXEC) == 0) {
      closedir(directory);
      return pdd_seal_error(env, PDD_SEAL_FAILURE_CLOEXEC_VERIFICATION);
    }
    sealed++;
  }
  if (errno != 0) {
    closedir(directory);
    return pdd_seal_error(env, PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_READ);
  }
  if (closedir(directory) != 0) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_DESCRIPTOR_TABLE_CLOSE);
  }
  if (sealed == 0) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_ALIAS_NOT_FOUND);
  }

  napi_value result;
  if (napi_create_uint32(env, sealed, &result) != napi_ok) {
    return pdd_seal_error(env, PDD_SEAL_FAILURE_RESPONSE_CREATION);
  }
  return result;
}

#ifdef PDD_TEST_EXEC_PROBE
/* Compiled only by the Linux regression harness, never in the shipped addon. */
static napi_value pdd_error(napi_env env, const char *message) {
  napi_throw_error(env, NULL, message);
  return NULL;
}

static napi_value pdd_probe_exec(napi_env env, napi_callback_info info) {
  size_t count = 5;
  napi_value arguments[5];
  size_t executable_size = 0;
  char *executable = NULL;
  int32_t first_fd = -1;
  int32_t second_fd = -1;
  uint64_t expected_device = 0;
  uint64_t expected_inode = 0;
  pid_t child;
  int status;
  char first_text[32];
  char second_text[32];
  char expected_device_text[32];
  char expected_inode_text[32];
  const char *script =
      "const fs=require('node:fs'); const device=BigInt(process.argv[3]); "
      "const inode=BigInt(process.argv[4]); for (const value of process.argv.slice(1,3)) "
      "{ try { const observed=fs.fstatSync(Number(value),{bigint:true}); "
      "if(observed.isFIFO()&&observed.dev===device&&observed.ino===inode)process.exit(7); "
      "} catch (_) {} }";

  if (napi_get_cb_info(env, info, &count, arguments, NULL, NULL) != napi_ok ||
      count != 5 ||
      napi_get_value_string_utf8(env, arguments[0], NULL, 0, &executable_size) !=
          napi_ok ||
      executable_size == 0 ||
      napi_get_value_int32(env, arguments[1], &first_fd) != napi_ok ||
      napi_get_value_int32(env, arguments[2], &second_fd) != napi_ok ||
      !pdd_bigint_argument(env, arguments[3], &expected_device) ||
      !pdd_bigint_argument(env, arguments[4], &expected_inode) ||
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
  snprintf(expected_device_text, sizeof(expected_device_text), "%llu",
           (unsigned long long)expected_device);
  snprintf(expected_inode_text, sizeof(expected_inode_text), "%llu",
           (unsigned long long)expected_inode);
  child = fork();
  if (child < 0) {
    free(executable);
    return pdd_error(env, "trusted Vitest exec probe fork failed");
  }
  if (child == 0) {
    execl(executable, executable, "-e", script, first_text, second_text,
          expected_device_text, expected_inode_text, (char *)NULL);
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
