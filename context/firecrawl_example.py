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

# Example 2: Automatic caching in PDD (recommended)
# When you use <web>URL</web> tags in prompts, PDD automatically:
# 1. Checks cache first (with URL normalization and tracking parameter removal)
# 2. Scrapes if not cached or expired
# 3. Caches the result with access tracking (24h default TTL)
# 4. Automatically cleans up expired entries
# 5. Enforces size limits with LRU eviction
#
# No manual cache management needed!

# Example 3: Cache configuration via environment variables
# Configure the cache behavior with these optional settings:

# export FIRECRAWL_CACHE_ENABLE=false          # Disable caching (default: true)
# export FIRECRAWL_CACHE_TTL_HOURS=48          # Cache for 48 hours (default: 24)
# export FIRECRAWL_CACHE_MAX_SIZE_MB=200       # Max cache size in MB (default: 100)
# export FIRECRAWL_CACHE_MAX_ENTRIES=2000      # Max number of entries (default: 1000)
# export FIRECRAWL_CACHE_AUTO_CLEANUP=false    # Disable auto cleanup (default: true)

# Example 4: Cache management CLI commands
# View cache statistics:
#   pdd firecrawl-cache stats
#
# Clear all cached entries:
#   pdd firecrawl-cache clear
#
# View cache configuration:
#   pdd firecrawl-cache info
#
# Check if a URL is cached:
#   pdd firecrawl-cache check https://example.com

# Example 5: Manual cache usage with advanced features (rarely needed)
# Most users don't need this - caching is automatic via <web> tags
from pdd.firecrawl_cache import get_firecrawl_cache
import time

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
        # Cache with custom TTL and metadata
        metadata = {
            'scraped_at': time.time(),
            'source': 'firecrawl',
            'format': 'markdown'
        }
        cache.set(url, content, ttl_hours=48, metadata=metadata)
        print(content)

# Example 6: View cache statistics programmatically
from pdd.firecrawl_cache import get_firecrawl_cache_stats

stats = get_firecrawl_cache_stats()
print(f"\nCache Statistics:")
print(f"  Total entries: {stats.get('total_entries', 0)}")
print(f"  Active entries: {stats.get('active_entries', 0)}")
print(f"  Expired entries: {stats.get('expired_entries', 0)}")
print(f"  Total size: {stats.get('total_size_mb', 0)} MB")
print(f"  Average access count: {stats.get('average_access_count', 0)}")
print(f"  Cache efficiency: {stats.get('cache_efficiency', 0)}%")
print(f"  Cache location: {stats.get('cache_path', 'N/A')}")

# Example 7: Cache features explained
#
# URL Normalization:
#   - URLs are normalized for consistent cache keys
#   - Tracking parameters (utm_*, fbclid, gclid, etc.) are removed
#   - Case-insensitive matching (HTTP://EXAMPLE.COM == http://example.com)
#   - Trailing slashes normalized (example.com/ == example.com)
#
# Access Tracking:
#   - Each cache hit increments access_count
#   - last_accessed timestamp updated on each access
#   - Used for LRU eviction when cache is full
#
# Automatic Cleanup:
#   - Expired entries removed automatically on set operations
#   - LRU eviction when max_entries limit is reached
#   - Ensures cache stays within configured size limits
#
# Cache Storage:
#   - SQLite database at: PROJECT_ROOT/.pdd/cache/firecrawl.db
#   - Persistent across sessions
#   - Efficient indexing for fast lookups
