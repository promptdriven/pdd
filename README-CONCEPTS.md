# PDD Fundamental Concepts and Practices
- [The Big Ideas](#the-big-ideas)
- [Adopt These Practices](#adopt-practices)
- [Conclusion](#conclusion)


<a name="the-big-ideas"></a>
# The Big Ideas

Prompt-Driven Development (PDD) treats prompts as the primary artifact - not code. This paradigm shift has profound implications:

- **Prompts as Source of Truth**<BR> 
   - In PDD, the prompts are authoritative, with code being a generated artifact, technically disposable.  By contrast, in traditional development, source code is the ground truth that defines system behavior. 

- **One Prompt per Output File**<br>
   - Each prompt is a natural-language mini-specification of a target output file.  This laser-focuses the LLM on the single target, reducing issues such as hallucination.
   
   - PDD's archtitecture and features gives the user precise control over what is in-context for each file generation - the main prompt, included modular prompt snippets describing dependencies, coding style preferences, etc.   
   
   - At the same time it eliminates from context irrelevant code snippets, chat history, etc. which confuses the models within tools such as Claude, Codex, etc.  Further, it uses fewer tokens, resulting in lower API costs (often 1/5 the cost of thos other tools)

- **Natural Language Over Code**<br>
   -   Prompts are written primarily in natural language, making them more accessible to non-programmers and clearer in expressing intent.

- **Regenerative Development**<br>
   - When changes are needed, you modify the prompt and fully regenerate the code, rather than directly editing the code. This maintains the conceptual integrity between requirements and implementation.

- **Intent Preservation**<br>
   - Natural language prompts capture the "why" behind code in addition to the "what" - preserving design rationale in a way that comments often fail to do.

<br>

<a name="adopt-practices"></a>
# Adopt These Practices

### 1. Prompts First:
   Always start by defining what you want in a prompt before generating any code.
   <br><br>
   Use tools like Cursor, ChatGPT, and even Claude Code as your co-pilot in this process.   You can also use these tools also to convert your product artifacts (PRDs, specs, design docs, etc.) into prompts, and keep them up to date, though we recommend an interim step (architecture.json) which we describe elsewhere.


### 2. Keep Prompts and Code in Sync:
   - Prompt → Code<br>
    Your "daily driver" - code generation with `pdd generate`
   
   - Code → Prompt<br>
    `pdd update` incorporates direct code changes into the original prompts.    Such changes may originate from PDD's automated test-diagnose-fix loops, from direct edits by a user, or changes with tools such as Claude.   Alternately, `pdd sync` will detect and invoke `pdd update` for prompts which are out of date.

### 3. Integrate Code Files via "Examples":
   "Examples" in PDD terminology are separate files of runnable code, showing how to use a specific target output file - they describe the interface for that code file.<br>
   
   Use `pdd example` to generate examples for any code file which will be used by another.<br>

   Then, in prompts for those other code files, `<include>` those examples as dependencies in your prompts.   `pdd auto-deps` will add `<include>` directives for these dependencies to a prompt file - and further, `pdd sync` will figure out which files need which dependencies, and apply `pdd auto-deps` for you.

   Examples are valuable artifacts which should be versioned in your project repository, along side your prompts.

### 4. Shape and Define Correct Code Behavior with Tests:
   PDD ensures correct code using tests which accumulate over the life of your project.   PDD's workflows using `pdd fix`, `pdd crash`, and `pdd verify` utilize these accumulated tests to test, verify and correct output code; `pdd sync` will also invoke these tools automatically.
   
   Generate unit tests with `pdd test`, and as bugs are found generate regression tests with `pdd bug`.   `Pdd sync` will also invoke `pdd test` and `pdd bug` when necessary.

   Tests, like examples, are valuable artifacts which should be versioned in your project repository, along side your prompts.


### 5. Modularize Prompts:
   Just as you modularize code, you should modularize prompts into self-contained units that can be composed.  Specifically, the PDD `<include>` tag directive enables you to incorporate modular units into any/all prompts.  
   <br>
   For example, you might want a single prompt unit describing your coding style preferences, which you then `<include>` in all your code prompt files.   
   
   Use `pdd auto-deps` to analyze dependencies between prompts/code, and automatically insert include directives for examples from each dependency into your prompt file(s).

<br>

<a name="conclusion"></a>
## Conclusion

Beyond the concepts and PDD commands mentioned above, PDD CLI provides a comprehensive set of tools for managing prompt files, generating code, creating examples, running tests, and handling various aspects of prompt-driven development. By leveraging the power of AI models and iterative processes, PDD aims to streamline the development workflow and improve code quality.

The various commands and options allow for flexible usage, from simple code generation to complex workflows involving multiple steps. The ability to track costs and manage output locations through environment variables further enhances the tool's utility in different development environments.

As you become more familiar with PDD, you can compose richer workflows by chaining commands in shell scripts, task runners, or CI pipelines while leveraging the full range of options available. Always refer to the latest documentation and use the built-in help features to make the most of PDD in your development process.

Remember to stay mindful of security considerations, especially when working with generated code or sensitive data. Regularly update PDD to access the latest features and improvements.

Happy coding with PDD!

