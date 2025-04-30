# Goal is to use DSPy to select the optimal example from change
# #first step set up . assume we have already linked to OpenAI API well
# import context.DSPy_example as DSPy_example #set up the LM
# turbo=dspy.OpenAI(model="gpt-3.5-turbo-instruct", max_tokens=250)
# dspy.settings.configure(lm=turbo)
                    
# #step 2. define the module
# class chainofthought(dspy.Module):
#     def __init__(self):
#         super()._init__()
#         self.prog=dspy.ChainOfThought("question->answer")
#     def forward(self, question):
#         return self.prog(question=question)
    
    #compile  and optimizer the     