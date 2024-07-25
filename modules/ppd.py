from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

# Read the template from a file
with open('./prompts/ppd.prompt', 'r') as file:
    template_content = file.read()

# Create the LCEL template
prompt_template = ChatPromptTemplate.from_messages([("user", template_content)])
llm = ChatOpenAI(model="gpt-4o-mini") 
# Combine with a model and parser
chain = prompt_template |llm| StrOutputParser()

# Run the template
result = chain.invoke({"input": "Your input here"})
print(result)