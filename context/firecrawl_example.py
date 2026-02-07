"""
Minimal example: Using Firecrawl for web scraping in PDD.

Install: pip install firecrawl-py
Set: export FIRECRAWL_API_KEY=your_api_key
"""

from firecrawl import Firecrawl
import os

api_key = os.environ.get('FIRECRAWL_API_KEY')
if not api_key:
    raise ValueError("FIRECRAWL_API_KEY not set")

app = Firecrawl(api_key=api_key)

# Scrape a URL and get markdown content
response = app.scrape('https://example.com', formats=['markdown'])

# Handle both dict response (new API) and object response (legacy)
if isinstance(response, dict) and 'markdown' in response:
    content = response['markdown']
elif hasattr(response, 'markdown'):
    content = response.markdown
else:
    content = None

print(content)

# Cache-aware example (for generated code that needs to minimize API calls):
from pdd.firecrawl_cache import get_firecrawl_cache

cache = get_firecrawl_cache()
url = 'https://example.com'

# Check cache first
cached = cache.get(url)
if cached:
    print(f"Using cached content")
    content = cached
else:
    # Scrape if not cached
    response = app.scrape(url, formats=['markdown'])
    if isinstance(response, dict) and 'markdown' in response:
        content = response['markdown']
    elif hasattr(response, 'markdown'):
        content = response.markdown
    else:
        content = None

    # Store in cache
    if content:
        cache.set(url, content, ttl_hours=24)
        print(f"Scraped and cached")

# Note: Caching is automatic when using <web>URL</web> tags in prompts.
# For cache management, use: pdd firecrawl-cache stats|clear|check|info
