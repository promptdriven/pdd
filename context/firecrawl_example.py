# Example: Using Firecrawl for web scraping in PDD
# Install with: pip install firecrawl-py

from firecrawl import Firecrawl
import os

# Example 1: Direct Firecrawl usage (standard API)
api_key = os.environ.get('FIRECRAWL_API_KEY', 'YOUR_API_KEY')
app = Firecrawl(api_key=api_key)

scrape_result = app.scrape('https://www.example.com', formats=['markdown'])

# Handle both dict response (new API) and object response (legacy)
if isinstance(scrape_result, dict) and 'markdown' in scrape_result:
    markdown_content = scrape_result['markdown']
elif hasattr(scrape_result, 'markdown'):
    markdown_content = scrape_result.markdown
else:
    markdown_content = None

print(markdown_content)

# Example 2: Caching is automatic in PDD
# When you use <web>URL</web> tags in prompts, PDD automatically:
# 1. Checks cache first
# 2. Scrapes if not cached or expired
# 3. Caches the result for future use (24h default TTL)
#
# No manual cache management needed.
#
# Optional: Control caching via environment variables:
# export FIRECRAWL_CACHE_DISABLE=1      # Disable caching
# export FIRECRAWL_CACHE_TTL_HOURS=48   # Cache for 48 hours

# Example 3: Manual cache usage (advanced - rarely needed)
# Most users don't need this - caching is automatic via <web> tags
from pdd.firecrawl_cache import get_firecrawl_cache

cache = get_firecrawl_cache()

url = 'https://www.example.com'

# Check cache first (automatic in normal usage)
cached_content = cache.get(url)
if cached_content:
    print(f"Using cached content for {url}")
    print(cached_content)
else:
    print(f"Scraping {url}...")
    scrape_result = app.scrape(url, formats=['markdown'])

    if isinstance(scrape_result, dict) and 'markdown' in scrape_result:
        content = scrape_result['markdown']
    elif hasattr(scrape_result, 'markdown'):
        content = scrape_result.markdown
    else:
        content = None

    if content:
        # Cache for 24 hours (automatic in normal usage)
        cache.set(url, content, ttl_hours=24)
        print(content)
