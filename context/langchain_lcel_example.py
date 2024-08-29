import os
from langchain_core.prompts import PromptTemplate
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain_core.output_parsers import StrOutputParser
from langchain_core.prompts import ChatPromptTemplate
from langchain_core.runnables import RunnablePassthrough, ConfigurableField

from langchain_fireworks import Fireworks 
from langchain_anthropic import ChatAnthropic
from langchain_openai import ChatOpenAI # Chatbot and conversational tasks
from langchain_openai import OpenAI # General language tasks
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_groq import ChatGroq
from langchain_together import Together

from langchain.callbacks.base import BaseCallbackHandler
from langchain.schema import LLMResult


# Define a base output parser (e.g., PydanticOutputParser)
from pydantic import BaseModel, Field


# Always setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))


# Create the LCEL template. Make note of the variable {topic} which will be filled in later.
prompt_template = PromptTemplate.from_template("Tell me a joke about {topic}")

llm = ChatGoogleGenerativeAI(model="gemini-pro", temperature=0)
# Combine with a model and parser to output a string
chain = prompt_template |llm| StrOutputParser()

# Run the template. Notice that the input is a dictionary with a single key "topic" which feeds it into the above prompt template. This is needed because the prompt template has a variable {topic} which needs to be filled in when invoked.
result = chain.invoke({"topic": "cats"})
print(result)


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

llm = ChatOpenAI(model="gpt-4o-mini", temperature=0, response_format={"type": "json_object"}) 

# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Tell me a joke."})
print("4o mini JSON: ",result)


# Get DEEKSEEK_API_KEY environmental variable
deepseek_api_key = os.getenv('DEEKSEEK_API_KEY')

# Ensure the API key is retrieved successfully
if deepseek_api_key is None:
    raise ValueError("DEEKSEEK_API_KEY environment variable is not set")

llm = ChatOpenAI(
    model='deepseek-chat', 
    openai_api_key=deepseek_api_key, 
    openai_api_base='https://api.deepseek.com',
    temperature=0
)

# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Write joke about the sky"})
print("deepseek",result)


llm = Fireworks(
    model="accounts/fireworks/models/mixtral-8x7b-instruct",
    temperature=0)
# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Tell me a joke about the president"})
print("fireworks",result)





prompt = ChatPromptTemplate.from_template(
    "Tell me a short joke about {topic}"
)
chat_openai = ChatOpenAI(model="gpt-3.5-turbo")
openai = OpenAI(model="gpt-3.5-turbo-instruct")
anthropic = ChatAnthropic(model="claude-2")
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



llm = ChatGroq(temperature=0, model_name="mixtral-8x7b-32768")
system = "You are a helpful assistant."
human = "{text}"
prompt = ChatPromptTemplate.from_messages([("system", system), ("human", human)])

chain = prompt | llm | StrOutputParser()
print(chain.invoke({"text": "Explain the importance of low latency LLMs."}))


llm = Together(
    model="meta-llama/Llama-3-70b-chat-hf",
    max_tokens=500,
)
chain = prompt | llm | StrOutputParser()
print(chain.invoke({"text": "Explain the importance of together.ai."}))


from langchain.prompts import PromptTemplate

# Define a prompt template with placeholders for variables
prompt_template = PromptTemplate.from_template("Tell me a {adjective} joke about {content}.")

# Format the prompt with the variables
formatted_prompt = prompt_template.format(adjective="funny", content="data scientists")

# Print the formatted prompt
print(formatted_prompt)



class CompletionStatusHandler(BaseCallbackHandler):
    def __init__(self):
        self.is_complete = False
        self.finish_reason = None

    def on_llm_end(self, response: LLMResult, **kwargs) -> None:
        self.is_complete = True
        if response.generations:
            self.finish_reason = response.generations[0][0].generation_info.get('finish_reason')

# Set up the LLM with the custom handler
handler = CompletionStatusHandler()
llm = ChatOpenAI(model="gpt-3.5-turbo", temperature=0.9, callbacks=[handler])

prompt = PromptTemplate.from_template("What is a good name for a company that makes {product}?")

chain = prompt | llm

# Run the chain
response = chain.invoke({"product":"colorful socks"})

# Check completion status
print(f"Is complete: {handler.is_complete}")
print(f"Finish reason: {handler.finish_reason}")
print(f"Response: {response}")