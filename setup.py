from setuptools import setup, find_packages

setup(
    name='pdd',
    version='0.1.0',
    packages=find_packages(),
    include_package_data=True,
    install_requires=[
        'anthropic==0.34.1',
        'click==8.1.7',
        'langchain==0.2.14',
        'langchain_anthropic==0.1.23',
        'langchain_community==0.2.12',
        'langchain_core==0.2.34',
        'pydantic==2.8.2',
        'rich==13.7.1',
        'tiktoken==0.7.0',
        'transformers==4.44.0'
    ],
    extras_require={
        'all': [
            'beautifulsoup4==4.12.3',
            'langchain_fireworks==0.1.7',
            'langchain_google_genai==1.0.10',
            'langchain_groq==0.1.9',
            'langchain_openai==0.1.22',
            'langchain_together==0.1.5',
            'pandas==2.2.2'
        ]
    },
    entry_points={
        'console_scripts': [
            'pdd = pdd.cli:cli',
        ],
    },
)