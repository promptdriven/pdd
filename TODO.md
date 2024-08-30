# TODO

## Features

- [ ] auto reflect
- [ ] run lint for context for better reflection
- [ ] smart includes
- [ ] auto-includes
- [ ] execute shell tools in ```<>``` <shell> </shell>
- [ ] auto split modules into another sub module
- [ ] auto check inconsistencies between modules
- [ ] implement changes across modules
- [ ] routlellm
- [ ] online database of examples to reference
- [ ] auto record which model works for each prompt
- [ ] benchmark fix the prompt based on diffs to the code file
- [ ] Use perplexica to automatically find context
- [ ] fix error messages when example runs
- [ ] infinite code generation
- [ ] execute up to a budget amount
- [ ] increase the number of unit tests to generate
- [ ] tally up all costs into a csv file
- [ ] use context caching during fixing errors
- [ ] debugger that matches prompt lines to code lines
- [ ] auto make new unit tests based on failures
- [ ] auto update the utility
- [ ] github login 
- [ ] Run on server based keys

## Bugs


## Improvements

- [ ] postprocess.prompt requires sonnet 3.5 and isn't stable
- [ ] read from a csv file the comment 
- [ ] total cost of makefile runs
- [ ] fix make file production and prepopulate
- [ ] put in context of the prompt for the fix
- [ ] have fix remember what was the closest code passing and start from that to hill climb
- [ ] Analyze errors first before trying to fix
- [ ] Check to see if unit test are aligned to the prompt
- [ ] Use existing good prompt code example to generate code for the prompt
- [ ] get the last github version of a file when trying to update instead of trying to find an old version

## Documentation

- [ ] Update README with installation instructions
