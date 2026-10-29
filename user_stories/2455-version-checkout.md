# Distinguish checkout builds in `pdd --version`

As a tester using a linked local checkout, I can identify that build in `pdd --version` and distinguish it from the release with its branch and commit.

## Acceptance criteria

1. Running `pdd --version` from a linked local checkout whose real package root is the Git top level prints the package version followed by `-dev.<encoded-branch>.<sha9>` for a symbolic branch, with `/` replaced by `-` and the first 9 hexadecimal commit characters, one newline, and no package-name prefix. A detached checkout prints the plain package version.
2. Running `pdd --version` from the published release or an npm-packed GitHub branch continues to print only the release version followed by one newline.

## Documentation deliverable

Repository usage documentation explains `npm install -g <local path>` and `node bin/pdd.mjs` for a linked checkout, and explains that GitHub branch installs are npm-packed and remain release-looking.
