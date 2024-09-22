from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setup(
    name="pdd",
    version="0.1.0",
    author="Greg Tanaka",
    author_email="glt@alumni.caltech.edu",
    description="A CLI tool for Prompt-Driven Development",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/gltanaka/PPD",
    packages=find_packages(),
    install_requires=[
        "GitPython==3.1.43",
        "anthropic==0.34.2",
        "click==8.1.7",
        "langchain==0.3.0",
        "langchain_anthropic==0.2.1",
        "langchain_community==0.3.0",
        "langchain_core==0.3.5",
        "langchain_fireworks==0.2.0",
        "langchain_google_genai==2.0.0",
        "langchain_groq==0.2.0",
        "langchain_openai==0.2.0",
        "langchain_together==0.2.0",
        "pandas==2.2.3",
        "pytest==8.3.2",
        "rich==13.8.1",
        "tiktoken==0.7.0",
        "transformers==4.44.0",
    ],
    entry_points={
        "console_scripts": [
            "pdd=pdd.cli:cli",
        ],
    },
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
    ],
    python_requires=">=3.7",
)