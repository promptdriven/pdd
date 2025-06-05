# TODO
- [ ] reasoning support, allow strength to go above 1 to allocate more thinking tokens via time parameter


## On Deck
- [ ] during fix rather than just have the fix loop check to see if the example crashed, have it use a llm to check if the results are largely correct still


## Features
- [ ] Have test and example use the cloud option for giving better context
- [ ] warming option for temperature increase
- [ ] strength option for strength increase
- [ ] use context caching during fixing errors
- [ ] auto reflect
- [ ] run lint for context for better reflection
- [ ] smart includes
- [ ] auto split modules into another sub module
- [ ] auto check inconsistencies between modules
- [ ] routlellm
- [ ] auto record which model works for each prompt
- [ ] agentic additional context inclusion via context 7 MCP
- [ ] Use perplexica to automatically find context
- [ ] create a marketplace where people can earn LLM credits for their examples or people can put up bounties for examples
- [ ] take a chat conversation and collapse down into a single prompt
- [ ] separate out the failing test and then run fix loop on that
- [ ] Use the prompts that use a certain module to generate tests for that module
- [ ] debug using pdb in non-interactive mode
- [ ] show what apis are available for a given module
- [ ] Cache webscraping results
- [ ] Retrieve what is most needed from a webscrape and condense it down
- [ ] test out anthropic think tool
- [ ] agentic prompt to code
- [ ] re-ranker for the example using a LLM
- [ ] syncing Makefile
- [ ] uv support, handle the ask the user to upgrade situation for uv
- [ ] integrate the csv llm model check into the cli and have it say the strength of the models
- [ ] Use codex for agentic mode
- [ ] add tests vs. writing overthem if test file exists
- [ ] update without need prior version of code


## Bugs
- [ ] jwt token issue when not signed in
- [ ] GCS bucket issue
- [ ] should print out after authentication is successful with github
- [ ] .env where PDD_PATH is instead of where the user runs the command

## Improvements
- [ ] update prompt for makefile
- [ ] fix make file production and prepopulate
- [ ] have fix remember what was the closest code passing and start from that to hill climb
- [ ] fix quiet vs. verbose ambiguity
- [ ] have a link from includes to the files for the vscode prompt extension
- [ ] have update touch the source file py so that the Make file doesn't go into infinite loop
- [ ] Anywhere cache https://cloud.google.com/storage/docs/anywhere-cache?hl=en&_gl=1*hrk570*_ga*MTM4MzA4MjkzMy4xNjcwNTM0ODI5*_ga_WH2QY8WWF5*czE3NDYzNzYwNjUkbzE2NyRnMSR0MTc0NjM3NjExMiRqMTMkbDAkaDA.
- [ ] fix the overlogging
- [ ] have landing page that allows people to take their chat history and make it a proper one shot prompt
- [ ] have landing page that allows people to take their code and give their prompt
- [ ] do a design compiler like strategy where you can retarget code to a different language

## Documentation
- [ ] make readme accessible via cli/mcp server
- [ ] develop a marketing readme