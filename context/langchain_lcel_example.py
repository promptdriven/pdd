from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_anthropic import ChatAnthropic
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain.output_parsers import RetryOutputParser

# Define a base output parser (e.g., PydanticOutputParser)
from pydantic import BaseModel, Field


# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))
# Create the LCEL template. Make note of the variable {topic} which will be filled in later.
prompt_template = PromptTemplate.from_template("Tell me a joke about {topic}")

llm = ChatOpenAI(model="gpt-4o-mini", temperature=0) 
# Combine with a model and parser to output a string
chain = prompt_template |llm| StrOutputParser()

# Run the template. Notice that the input is a dictionary with a single key "topic" which feeds it into the above prompt template. This is needed because the prompt template has a variable {topic} which needs to be filled in when invoked.
result = chain.invoke({"topic": "cats"})
print(result)


# Define your desired data structure.
class Joke(BaseModel):
    setup: str = Field(description="question to set up a joke")
    punchline: str = Field(description="answer to resolve the joke")


llm = ChatGoogleGenerativeAI(model="gemini-pro", temperature=0)
# Set up a parser
parser = JsonOutputParser(pydantic_object=Joke)

# Create a prompt template
prompt = PromptTemplate(
    template="Answer the user query.\n{format_instructions}\n{query}\n",
    input_variables=["query"],
    partial_variables={"format_instructions": parser.get_format_instructions()},
)

# Chain the components
chain = prompt | llm | parser

# Invoke the chain with a query
result = chain.invoke({"query": "Tell me a joke."})
print(result)



class Action(BaseModel):
    action: str
    action_input: str = Field(description="Input for the action")

# Initialize the LLM
llm = ChatAnthropic(model='claude-3-opus-20240229', temperature=0)

# Create the RetryOutputParser
retry_parser = RetryOutputParser.from_llm(parser=Action, llm=llm)

# Example of a bad response
bad_response = '{"action": "search"}'  # Missing action_input

# Attempt to parse the bad response with the retry parser
parsed_result = retry_parser.parse_with_prompt(bad_response, prompt_value="Please provide a valid action with input.")
print(parsed_result)