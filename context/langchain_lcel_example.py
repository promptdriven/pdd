import os
from langchain_core.prompts import PromptTemplate
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.output_parsers import JsonOutputParser, PydanticOutputParser # Parsers are only avaiable in langchain_core.output_parsers not langchain.output_parsers
from langchain_core.output_parsers import StrOutputParser
from langchain_core.prompts import ChatPromptTemplate
from langchain_core.runnables import RunnablePassthrough, ConfigurableField

from langchain_openai import AzureChatOpenAI
from langchain_fireworks import Fireworks 
from langchain_anthropic import ChatAnthropic
from langchain_openai import ChatOpenAI # Chatbot and conversational tasks
from langchain_openai import OpenAI # General language tasks
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_google_vertexai import ChatVertexAI
from langchain_groq import ChatGroq
from langchain_together import Together

from langchain.callbacks.base import BaseCallbackHandler
from langchain.schema import LLMResult



# Define a base output parser (e.g., PydanticOutputParser)
from pydantic import BaseModel, Field

import json

class CompletionStatusHandler(BaseCallbackHandler):
    def __init__(self):
        self.is_complete = False
        self.finish_reason = None
        self.input_tokens = None
        self.output_tokens = None

    def on_llm_end(self, response: LLMResult, **kwargs) -> None:
        self.is_complete = True
        if response.generations and response.generations[0]:
            generation = response.generations[0][0]
            self.finish_reason = generation.generation_info.get('finish_reason').lower()
            
            # Extract token usage
            if hasattr(generation.message, 'usage_metadata'):
                usage_metadata = generation.message.usage_metadata
                self.input_tokens = usage_metadata.get('input_tokens')
                self.output_tokens = usage_metadata.get('output_tokens')
        # print("response:",response)
        print(f"Extracted information:")
        print(f"Finish reason: {self.finish_reason}")
        print(f"Input tokens: {self.input_tokens}")
        print(f"Output tokens: {self.output_tokens}")

# Set up the LLM with the custom handler
handler = CompletionStatusHandler()
# Always setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))


# Create the LCEL template. Make note of the variable {topic} which will be filled in later.
prompt_template = PromptTemplate.from_template("Tell me a joke about {topic}")

llm = ChatGoogleGenerativeAI(model="gemini-pro", temperature=0, callbacks=[handler])
# Combine with a model and parser to output a string
chain = prompt_template |llm| StrOutputParser()

# Run the template. Notice that the input is a dictionary with a single key "topic" which feeds it into the above prompt template. This is needed because the prompt template has a variable {topic} which needs to be filled in when invoked.
result = chain.invoke({"topic": "cats"})
print("********Google:", result)


llm = ChatVertexAI(model="gemini-pro", temperature=0, callbacks=[handler])
# Combine with a model and parser to output a string
chain = prompt_template |llm| StrOutputParser()

# Run the template. Notice that the input is a dictionary with a single key "topic" which feeds it into the above prompt template. This is needed because the prompt template has a variable {topic} which needs to be filled in when invoked.
result = chain.invoke({"topic": "cats"})
print("********GoogleVertex:", result)


# Define your desired data structure.
class Joke(BaseModel):
    setup: str = Field(description="question to set up a joke")
    punchline: str = Field(description="answer to resolve the joke")


# Set up a parser
parser = JsonOutputParser(pydantic_object=Joke)

# Create a prompt template
prompt = PromptTemplate(
    template="Answer the user query.\n{format_instructions}\n{query}\n",
    input_variables=["query"],
    partial_variables={"format_instructions": parser.get_format_instructions()},
)

llm_no_struct = ChatOpenAI(model="gpt-4o-mini", temperature=0, 
                           callbacks=[handler]) 
llm = llm_no_struct.with_structured_output(Joke) # with structured output forces the output to be a specific object, in this case Joke. Only OpenAI models have structured output
# Chain the components. 
#  The class `LLMChain` was deprecated in LangChain 0.1.17 and will be removed in 1.0. Use RunnableSequence, e.g., `prompt | llm` instead.
chain = prompt | llm 

# Invoke the chain with a query. 
# IMPORTANT: chain.run is now obsolete. Use chain.invoke instead.
result = chain.invoke({"query": "Tell me a joke about openai."})
print("4o mini JSON: ",result)
print(result.setup) # How to access the structured output

llm = ChatOpenAI(model="o1", temperature=1, 
                           callbacks=[handler],model_kwargs = {"max_completion_tokens" : 1000})
# Chain the components. 
#  The class `LLMChain` was deprecated in LangChain 0.1.17 and will be removed in 1.0. Use RunnableSequence, e.g., `prompt | llm` instead.
chain = prompt | llm | parser

# Invoke the chain with a query. 
# IMPORTANT: chain.run is now obsolete. Use chain.invoke instead.
result = chain.invoke({"query": "Tell me a joke about openai."})
print("o1 JSON: ",result)

# Get DEEPSEEK_API_KEY environmental variable

deepseek_api_key = os.getenv('DEEPSEEK_API_KEY')

# Ensure the API key is retrieved successfully
if deepseek_api_key is None:
    raise ValueError("DEEPSEEK_API_KEY environment variable is not set")

llm = ChatOpenAI(
    model='deepseek-chat', 
    openai_api_key=deepseek_api_key, 
    openai_api_base='https://api.deepseek.com',
    temperature=0, callbacks=[handler]
)

# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Write joke about deepseek."})
print("deepseek",result)


# Set up a parser
parser = PydanticOutputParser(pydantic_object=Joke)
# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Write joke about deepseek and pydantic."})
print("deepseek pydantic",result)

# Set up the Azure ChatOpenAI LLM instance
llm_no_struct = AzureChatOpenAI(
    model="o1-mini-2024-09-12",
    temperature=0,
    callbacks=[handler]
)
llm = llm_no_struct.with_structured_output(Joke) # with structured output forces the output to be a specific JSON format
# Chain the components: prompt | llm | parser
chain = prompt | llm # returns a Joke object

# Invoke the chain with a query
result = chain.invoke({"query": "What is Azure?"})  # Pass a dictionary if `invoke` expects it
print("Azure Result:", result)

# Set up a parser
parser = JsonOutputParser(pydantic_object=Joke)

llm = Fireworks(
    model="accounts/fireworks/models/mixtral-8x7b-instruct",
    temperature=0, callbacks=[handler])
# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Tell me a joke about the president"})
print("fireworks",result)





prompt = ChatPromptTemplate.from_template(
    "Tell me a short joke about {topic}"
)
chat_openai = ChatOpenAI(model="gpt-3.5-turbo", callbacks=[handler])
openai = OpenAI(model="gpt-3.5-turbo-instruct", callbacks=[handler])
anthropic = ChatAnthropic(model="claude-2", callbacks=[handler])
model = (
    chat_openai
    .with_fallbacks([anthropic])
    .configurable_alternatives(
        ConfigurableField(id="model"),
        default_key="chat_openai",
        openai=openai,
        anthropic=anthropic,
    )
)

chain = (
    {"topic": RunnablePassthrough()} 
    | prompt 
    | model 
    | StrOutputParser()
)
result = chain.invoke({"topic": "Tell me a joke about the president"})
print("config alt:",result)



llm = ChatGroq(temperature=0, model_name="mixtral-8x7b-32768", callbacks=[handler])
system = "You are a helpful assistant."
human = "{text}"
prompt = ChatPromptTemplate.from_messages([("system", system), ("human", human)])

chain = prompt | llm | StrOutputParser()
print(chain.invoke({"text": "Explain the importance of low latency LLMs."}))


llm = Together(
    model="meta-llama/Llama-3-70b-chat-hf",
    max_tokens=500, callbacks=[handler]
)
chain = prompt | llm | StrOutputParser()
print(chain.invoke({"text": "Explain the importance of together.ai."}))


# Define a prompt template with placeholders for variables
prompt_template = PromptTemplate.from_template("Tell me a {adjective} joke about {content}.")

# Format the prompt with the variables
formatted_prompt = prompt_template.format(adjective="funny", content="data scientists")

# Print the formatted prompt
print(formatted_prompt)


# Set up the LLM with the custom handler
handler = CompletionStatusHandler()


llm = ChatOpenAI(model="gpt-3.5-turbo", temperature=0.9, callbacks=[handler])

prompt = PromptTemplate.from_template("What is a good name for a company that makes {product}?")

chain = prompt | llm

# Invoke the chain
response = chain.invoke({"product":"colorful socks"})

# Check completion status
print(f"Is complete: {handler.is_complete}")
print(f"Finish reason: {handler.finish_reason}")
print(f"Response: {response}")
print(f"Input tokens: {handler.input_tokens}")
print(f"Output tokens: {handler.output_tokens}")

from langchain_core.prompts import ChatPromptTemplate
from langchain_ollama.llms import OllamaLLM

template = """Question: {question}"""

prompt = ChatPromptTemplate.from_template(template)

model = OllamaLLM(model="qwen2.5-coder:32b")

chain = prompt | model

output = chain.invoke({"question": "Write a python function that calculates Pi"})
print(output)