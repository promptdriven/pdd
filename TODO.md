# TODO
- [ ] Python 3.13 support
- [ ] MCP wrapper for the CLI

## On Deck


## Features
- [ ] auto reflect
- [ ] run lint for context for better reflection
- [ ] smart includes
- [ ] auto split modules into another sub module
- [ ] auto check inconsistencies between modules
- [ ] routlellm
- [ ] auto record which model works for each prompt
- [ ] Use perplexica to automatically find context
- [ ] use context caching during fixing errors
- [ ] create a marketplace where people can earn LLM credits for their examples or people can put up bounties for examples
- [ ] take a chat conversation and collapse down into a single prompt
- [ ] warming option for temperature increase
- [ ] strength option for strength increase
- [ ] during fix rather than just have the fix loop check to see if the example crashed, have it use a llm to check if the results are largely correct still
- [ ] separate out the failing test and then run fix loop on that
- [ ] Use the prompts that use a certain module to generate tests for that module
- [ ] debug using pdb in non-interactive mode
- [ ] show what apis are available for a given module
- [ ] Cache webscraping results
- [ ] Retrieve what is most needed from a webscrape and condense it down
- [ ] test out anthropic think tool
- [ ] autogenerate the model.csv file and print out the strength of each model
- [ ] agentic prompt to code
- [ ] agentic additional context inclusion

## Bugs

## Improvements
- [ ] ask for and store API keys
- [ ] display model list
- [ ] read from a csv file the comment 
- [ ] fix make file production and prepopulate
- [ ] have fix remember what was the closest code passing and start from that to hill climb
- [ ] Analyze errors first before trying to fix
- [ ] Use existing good prompt code example to generate code for the prompt
- [ ] update prompt for makefile
- [ ] MLX support for faster local
- [ ] AWS Nova support
- [ ] fix quiet vs. verbose ambiguity
- [ ] reasoning support, allow strength to go above 1 to allocate more thinking tokens


## Documentation

- [ ] Update README with usage
- [ ] Model support