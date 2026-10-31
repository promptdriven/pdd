# Run a check from a script without leaving its input open

I can run pdd from a script whose input comes from an SSH connection and get control back when the command finishes, without a helper keeping that input open.

## Acceptance criteria

1. After `pdd test` or `pdd lint` exits, no helper started by that command retains the script's original input socket, including when a helper continues running.
2. Noninteractive Git lookups do not read the script's input, and their normal results and errors remain unchanged.
3. GitHub sign-in lookups and opening a Try link keep their existing isolated input behavior; pdd's interactive approvals and explicitly requested Try shell keep their terminal input behavior.

## Rules to check

The original input socket's identity matters: a separate pipe or socket created for a child is not the caller's input. A surviving helper holding the original socket is forbidden even when pdd has already printed its summary and exited. Verify the socket identity after pdd exits, with the harness's own copy closed.

## Native verification boundary

Inherited operating-system file descriptors are a native effect unsupported by the prompt runtime's result, world and call-count observations. Verify this Story by running the actual CLI against the local fake runtime, with socket-backed stdin and a controllable native helper. An independent helper deliberately holding the caller's socket must be detected as a negative control. A simulated answer about descriptor ownership is not proof.

This is defensive isolation and a warning-light regression. The historical SSH hang has not been attributed to pdd, and the original-socket assertion currently passes on alpha. This Story does not claim to reproduce or resolve that historical cause.
