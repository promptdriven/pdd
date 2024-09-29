import os
from setuptools import setup, find_packages

# Read the contents of README.md for the long description
with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

# Define the requirements, excluding any commented-out lines
requirements = [
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
]

setup(
    name="pdd",
    version="0.2.0",
    author="Greg Tanaka",
    author_email="glt@alumni.caltech.edu",
    description="PDD (Prompt-Driven Development) Command Line Interface",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/gltanaka/PPD.git",
    packages=find_packages(exclude=["tests", "docs"]),
    install_requires=requirements,
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Operating System :: OS Independent",
        "Environment :: Console",
        "Topic :: Software Development :: Code Generators",
    ],
    python_requires=">=3.7",
    entry_points={
        "console_scripts": [
            "pdd=pdd.cli:cli",
        ],
    },
    include_package_data=True,
    keywords=[
        "prompt-driven development",
        "code generation",
        "CLI",
        "AI-assisted development",
        "unit testing",
        "code management",
    ],
    project_urls={
        "Bug Reports": "https://github.com/gltanaka/PPD/issues",
        "Source": "https://github.com/gltanaka/PPD.git",
    },
    license="MIT",
)