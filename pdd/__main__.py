"""Allow ``python -m pdd ...`` to invoke the same CLI as the ``pdd`` script.

The package's console-script entry point is ``pdd = "pdd.cli:cli"`` (see
``pyproject.toml``). Without this module, ``python -m pdd`` raises
``No module named pdd.__main__``, which breaks subprocess invocations that
prefer ``sys.executable -m pdd`` for venv parity (so the subprocess uses the
same interpreter and installed package as the caller, regardless of which
``pdd`` binary is first on PATH).
"""
from pdd.cli import cli


if __name__ == "__main__":
    cli()
