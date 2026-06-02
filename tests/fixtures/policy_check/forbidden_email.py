"""Notifier that sends email despite the contract."""

import smtplib


def notify() -> None:
    smtplib.SMTP("localhost").sendmail("a@b.c", "d@e.f", "body")
