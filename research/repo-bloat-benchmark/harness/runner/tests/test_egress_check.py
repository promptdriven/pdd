"""Offline tests for the container-tier egress checker.

The kernel-level properties themselves can only be verified inside the
Linux container (see container/README.md); these tests pin the checker's
*logic* — CONNECT status parsing, allow/deny verdicts, loopback probe —
against a local fake gateway, so a regression in the script fails here
rather than on the pilot machine.
"""

from __future__ import annotations

import socket
import threading

import harness.runner.container.egress_check as egress_check


class _FakeGateway:
    """Answers HTTP CONNECT: 200 for the allowed host, 403 otherwise."""

    def __init__(self, allowed_host: str) -> None:
        self.allowed_host = allowed_host
        self._server = socket.socket()
        self._server.bind(("127.0.0.1", 0))
        self._server.listen(4)
        self.port = self._server.getsockname()[1]
        threading.Thread(target=self._serve, daemon=True).start()

    def _serve(self) -> None:
        while True:
            try:
                conn, _ = self._server.accept()
            except OSError:
                return
            with conn:
                head = conn.recv(1024).decode("latin-1", errors="replace")
                target = head.split()[1] if len(head.split()) > 1 else ""
                if target.startswith(self.allowed_host + ":"):
                    conn.sendall(b"HTTP/1.1 200 Connection established\r\n\r\n")
                else:
                    conn.sendall(b"HTTP/1.1 403 Filtered\r\n\r\n")

    def close(self) -> None:
        self._server.close()


def test_gateway_connect_parses_allow_and_deny(monkeypatch):
    gateway = _FakeGateway(allowed_host="api.openai.com")
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{gateway.port}")
    try:
        assert egress_check._gateway_connect("api.openai.com", 443) == 200
        assert egress_check._gateway_connect("example.com", 443) == 403
    finally:
        gateway.close()


def test_runner_checks_pass_with_conforming_gateway(monkeypatch):
    """Runner role: ACL gateway grants the provider, refuses other hosts."""
    gateway = _FakeGateway(allowed_host="api.openai.com")
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{gateway.port}")
    monkeypatch.setattr(egress_check, "PROVIDER_HOST", "api.openai.com")
    # Force the "outside" probes to unroutable addresses so they fail fast.
    monkeypatch.setattr(egress_check, "OUTSIDE_TCP_PROBES", (("192.0.2.1", 443),))
    monkeypatch.setattr(egress_check, "OUTSIDE_UDP_PROBES", (("192.0.2.2", 53),))
    monkeypatch.setattr(egress_check, "OUTSIDE_IPV6_PROBES", (("2001:db8::1", 443),))
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    try:
        checks = egress_check.runner_checks()
        assert checks["gateway_reachable"] is True
        assert checks["gateway_allows_pinned_provider"] is True
        assert checks["gateway_blocks_other_hosts"] is True
    finally:
        gateway.close()


def test_agent_checks_flag_reachable_gateway_as_failure(monkeypatch):
    """Agent role: a REACHABLE gateway is a lockdown failure (bypass path)."""
    gateway = _FakeGateway(allowed_host="api.openai.com")
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{gateway.port}")
    monkeypatch.setattr(egress_check, "_http_healthcheck_ok", lambda base_url: True)
    monkeypatch.setattr(egress_check, "OUTSIDE_TCP_PROBES", (("192.0.2.1", 443),))
    monkeypatch.setattr(egress_check, "OUTSIDE_UDP_PROBES", (("192.0.2.2", 53),))
    monkeypatch.setattr(egress_check, "OUTSIDE_IPV6_PROBES", (("2001:db8::1", 443),))
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    try:
        checks = egress_check.agent_checks(proxy_url="http://runner:8080")
        # gateway is reachable here → the bypass guard must report failure...
        assert checks["gateway_unreachable_from_agent"] is False
        # ...while the proxy-reachable and loopback checks still pass.
        assert checks["recording_proxy_reachable"] is True
        assert checks["loopback_works"] is True
    finally:
        gateway.close()


def test_gateway_connect_none_when_gateway_down(monkeypatch):
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        dead_port = probe.getsockname()[1]
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{dead_port}")
    assert egress_check._gateway_connect("api.openai.com", 443) is None


def test_tcp_connect_true_on_listener_false_on_closed_port():
    listener = socket.socket()
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)
    port = listener.getsockname()[1]
    try:
        assert egress_check._tcp_connect("127.0.0.1", port) is True
    finally:
        listener.close()
    assert egress_check._tcp_connect("127.0.0.1", port) is False


def test_load_proxy_url_prefers_endpoint_json(tmp_path):
    path = tmp_path / "proxy.json"
    path.write_text('{"base_url": "http://runner:43123"}\n', encoding="utf-8")
    assert egress_check._load_proxy_url(str(path), None) == "http://runner:43123"
