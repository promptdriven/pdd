"""Real terminal driver; no network or provider calls, only owned scratch files."""
import errno
import json
import os
from pathlib import Path
import pty
import select
import signal
import subprocess
import sys
import tempfile
import time

scenario = sys.argv[1]
child = Path(__file__).with_name('live-local-consent-child.mjs')
prompt = b'Type yes to confirm:'
output = bytearray()

with tempfile.TemporaryDirectory(prefix='pdd-consent-') as scratch:
    master, slave = pty.openpty()
    process = subprocess.Popen([os.environ.get('PDD_TEST_NODE', 'node'), str(child), scenario, scratch], stdin=slave, stdout=slave, stderr=slave)
    os.close(slave)
    if scenario == 'pretyped':
        os.write(master, b'yes\n')
    elif scenario == 'pretyped-partial':
        os.write(master, b'yes')

    def read_for(seconds):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            if select.select([master], [], [], min(0.02, max(0, deadline - time.monotonic())))[0]:
                try:
                    data = os.read(master, 65536)
                except OSError as error:
                    if error.errno == errno.EIO:
                        return
                    raise
                if not data:
                    return
                output.extend(data)

    def until(predicate, message):
        deadline = time.monotonic() + 6
        while not predicate() and time.monotonic() < deadline:
            read_for(0.02)
        assert predicate(), message

    def has(text):
        return text.encode() in output

    def marker(id):
        return (Path(scratch) / 'workspace' / ('marker-' + id)).exists()

    try:
        until(lambda: prompt in output, 'First confirmation prompt must appear')
        read_for(0.15)
        assert output.count(prompt) == 1, 'Concurrent calls must display only one consent prompt'
        first = 'B' if b'"marker-B"' in output else 'A'
        second = 'A' if first == 'B' else 'B'
        assert not has('DONE'), 'No call may settle before its terminal answer'
        assert not marker('A') and not marker('B'), 'No physical write before consent'
        if scenario == 'interrupt-typeahead':
            os.write(master, b'\x03yes\n')
        elif scenario == 'decline-typeahead':
            os.write(master, b'no\nyes\n')
        elif scenario == 'interrupt':
            os.write(master, b'\x03')
        elif scenario == 'close':
            os.write(master, b'\x04')
        elif scenario == 'read-error':
            process.send_signal(signal.SIGUSR1)
        elif scenario == 'eof':
            process.send_signal(signal.SIGUSR2)
        elif scenario == 'decline':
            os.write(master, b'no\n')
        elif scenario in ('blank', 'pretyped-partial'):
            os.write(master, b'\n')
        elif scenario == 'typeahead':
            os.write(master, b'yes\nyes\n')
        elif scenario == 'partial-typeahead':
            os.write(master, b'yes\nyes')
        else:
            os.write(master, b'yes\n')

        first_confirmed = scenario not in ('interrupt', 'interrupt-typeahead', 'close', 'read-error', 'eof', 'decline', 'decline-typeahead', 'blank', 'pretyped-partial')
        until(lambda: has('DONE ' + first + ' '), 'First answer must settle only its call')
        assert has('DONE ' + first + ' ' + json.dumps({'confirmed': first_confirmed}, separators=(',', ':'))), 'First result must match its own answer'
        if scenario == 'eof':
            until(lambda: has('COMPLETE'), 'EOF must release and decline all queued confirmations')
            assert has('DONE B {"confirmed":false}'), 'EOF must not grant queued consent'
        else:
            until(lambda: output.count(prompt) == 2, 'Second call must get its own prompt after first settles')
            read_for(0.15)
            assert not has('DONE ' + second + ' '), 'One terminal answer must not authorize two calls'
            assert not marker(second), 'Second physical write must wait for its own consent'
            if scenario in ('execute', 'bridge'):
                assert marker(first), 'First physical write must run after its own consent'
                assert has('STARTED request-' + first) and not has('STARTED request-' + second), 'Started permits must follow each call consent'
            if scenario == 'partial-typeahead':
                os.write(master, b'\n')
                second_confirmed = False
            else:
                os.write(master, b'yes\n')
                second_confirmed = True
            until(lambda: has('COMPLETE'), 'Fresh second answer must settle queued call')
            assert has('DONE ' + second + ' ' + json.dumps({'confirmed': second_confirmed}, separators=(',', ':'))), 'Second result must use only its fresh answer'
            if scenario in ('execute', 'bridge'):
                assert marker('A') and marker('B'), 'Each approved call must perform its own scratch write'
        process.wait(timeout=3)
        assert process.returncode == 0, 'Native child must exit cleanly after queue release'
        print(json.dumps({'scenario': scenario, 'passed': True, 'physical_writes': 2 if scenario in ('execute', 'bridge') else 0, 'provider_calls': 0}))
    except BaseException:
        print(output.decode(errors='replace'), file=sys.stderr)
        raise
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        os.close(master)
