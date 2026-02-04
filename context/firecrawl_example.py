# Example: Using Firecrawl with caching for web scraping
# Install with: pip install firecrawl-py

from firecrawl import Firecrawl
from pdd.firecrawl_cache import get_firecrawl_cache
import os

# Example 1: Direct Firecrawl usage (main's API)
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

# Example 2: Using Firecrawl with caching (PR #151 feature)
cache = get_firecrawl_cache()

url = 'https://www.example.com'

# Check cache first
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
        # Cache for 24 hours
        cache.set(url, content, ttl_hours=24, metadata={'scraped_at': 'now'})
        print(content)

# Example 3: Cache management
cache_stats = cache.get_stats()
print(f"Cache has {cache_stats.get('total_entries', 0)} entries")

# Clear expired entries
# cache.clear()