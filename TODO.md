# TODO

## On Deck
- [ ] add loop to crash command like with fix
- [ ] auto-includes
- [ ] increase the number of unit tests to generate
- [ ] auto update the utility
- [ ] auto set PDD_PATH for package install

## Features

- [ ] auto reflect
- [ ] run lint for context for better reflection
- [ ] smart includes
- [ ] auto split modules into another sub module
- [ ] auto check inconsistencies between modules
- [ ] routlellm
- [ ] online database of examples to reference
- [ ] auto record which model works for each prompt
- [ ] benchmark fix the prompt based on diffs to the code file
- [ ] Use perplexica to automatically find context
- [ ] use context caching during fixing errors
- [ ] github login 
- [ ] Run on server based keys
- [ ] create a marketplace where people can earn LLM credits for their examples or people can put up bounties for examples
- [ ] ability to check in known good examples
- [ ] take a chat conversation and collapse down into a single prompt
- [ ] warming option for temperature increase
- [ ] VS code for prompt editing/display
- [ ] during fix rather than just have the fix loop check to see if the example crashed, have it use a llm to check if the results are largely correct still
- [ ] separate out the failing test and then run fix loop on that

## Bugs

- [ ] Fix change command fixing

## Improvements

- [ ] read from a csv file the comment 
- [ ] fix make file production and prepopulate
- [ ] have fix remember what was the closest code passing and start from that to hill climb
- [ ] Analyze errors first before trying to fix
- [ ] Use existing good prompt code example to generate code for the prompt
- [ ] update prompt for makefile
- [ ] fix warnings in the code
- [ ] fix toml file
- [ ] MLX support for faster local


## Documentation

- [ ] Update README with installation instructions