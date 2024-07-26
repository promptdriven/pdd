from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

# prompt is a BasePromptTemplate, which means it takes in a dictionary of template variables and produces a PromptValue. A PromptValue is a wrapper around a completed prompt that can be passed to either an LLM (which takes a string as input) or ChatModel (which takes a sequence of messages as input). It can work with either language model type because it defines logic both for producing BaseMessages and for producing a string.
# Create the LCEL template
prompt_template = PromptTemplate.from_template("Tell me a joke about {topic}")

llm = ChatOpenAI(model="gpt-4o-mini") 
# Combine with a model and parser
chain = prompt_template |llm| StrOutputParser()

# Run the template. Notice that the input is a dictionary with a single key "topic" which feeds it into the above prompt template. This is needed because the prompt template has a variable {topic} which needs to be filled in.
result = chain.invoke({"topic": "cats"})
print(result)