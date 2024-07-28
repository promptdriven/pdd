from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

# Create the LCEL template. Make note of the variable {topic} which will be filled in later.
prompt_template = PromptTemplate.from_template("Tell me a joke about {topic}")

llm = ChatOpenAI(model="gpt-4o-mini") 
# Combine with a model and parser to output a string
chain = prompt_template |llm| StrOutputParser()

# Run the template. Notice that the input is a dictionary with a single key "topic" which feeds it into the above prompt template. This is needed because the prompt template has a variable {topic} which needs to be filled in when invoked.
result = chain.invoke({"topic": "cats"})
print(result)