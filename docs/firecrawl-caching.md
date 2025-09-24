# Firecrawl Caching

This document describes the Firecrawl caching functionality implemented to address issue #46: "Cache firecrawl results so it doesn't use up the API credit".

## Overview

The Firecrawl caching system reduces API credit usage by storing scraped web content locally and serving cached results for subsequent requests within the configured cache duration. This is particularly useful for:

- Development and testing environments
- Documentation sites that don't change frequently
- Bulk processing jobs
- Reducing costs for repeated scraping of the same URLs

## Features

### Core Functionality
- **Persistent Caching**: SQLite-based storage for reliable caching across sessions
- **Configurable TTL**: Set cache duration per request or globally
- **URL Normalization**: Consistent cache keys by normalizing URLs (removing tracking parameters, case-insensitive)
- **Automatic Cleanup**: Expired entries are automatically removed
- **Size Management**: Configurable limits on cache size and number of entries
- **Access Tracking**: Monitor cache usage and efficiency

### Integration
- **Seamless Integration**: Works transparently with existing `<web>` tags in prompts
- **Firecrawl API Integration**: Uses Firecrawl's built-in `maxAge` parameter for server-side caching
- **Dual-Layer Caching**: Combines client-side and server-side caching for maximum efficiency

## Configuration

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `FIRECRAWL_CACHE_ENABLE` | `true` | Enable/disable caching |
| `FIRECRAWL_CACHE_TTL_HOURS` | `24` | Default cache TTL in hours |
| `FIRECRAWL_CACHE_MAX_SIZE_MB` | `100` | Maximum cache size in MB |
| `FIRECRAWL_CACHE_MAX_ENTRIES` | `1000` | Maximum number of cache entries |
| `FIRECRAWL_CACHE_AUTO_CLEANUP` | `true` | Enable automatic cleanup |
| `FIRECRAWL_API_KEY` | Required | Firecrawl API key for scraping |

### Example Configuration

```bash
# Enable caching with 48-hour TTL
export FIRECRAWL_CACHE_TTL_HOURS=48

# Set cache size limit to 200MB
export FIRECRAWL_CACHE_MAX_SIZE_MB=200

# Disable caching for real-time data
export FIRECRAWL_CACHE_ENABLE=false
```

## Usage

### Automatic Usage

The caching system works automatically with existing `<web>` tags in your prompts:

```prompt
# This will use cached content if available
<web>https://docs.example.com/api-reference</web>
```

### CLI Commands

#### View Cache Statistics
```bash
pdd firecrawl-cache stats
```

Shows:
- Total and active cache entries
- Cache size and efficiency
- Access patterns and statistics

#### Clear Cache
```bash
pdd firecrawl-cache clear
```

Removes all cached entries (with confirmation prompt).

#### Check Specific URL
```bash
pdd firecrawl-cache check --url https://example.com
```

Shows whether a specific URL is cached and displays content preview.

#### View Configuration
```bash
pdd firecrawl-cache info
```

Displays current cache configuration and environment variables.

### Programmatic Usage

```python
from pdd.firecrawl_cache import get_firecrawl_cache

# Get cache instance
cache = get_firecrawl_cache()

# Check if URL is cached
content = cache.get("https://example.com")
if content is None:
    # URL not cached, would need to scrape
    pass

# Cache content manually
cache.set("https://example.com", "web content", ttl_hours=12)

# Get cache statistics
stats = cache.get_stats()
print(f"Cache efficiency: {stats['active_entries']}/{stats['total_entries']}")
```

## Cache Storage

### Location
- **Default**: `{project_root}/cache/firecrawl/firecrawl_cache.db`
- **Custom**: Set via `FirecrawlCache(cache_dir="/path/to/cache")`

### Database Schema
```sql
CREATE TABLE cache_entries (
    url_hash TEXT PRIMARY KEY,      -- SHA256 hash of normalized URL
    url TEXT NOT NULL,              -- Original URL
    content TEXT NOT NULL,          -- Cached content
    timestamp REAL NOT NULL,        -- When cached
    expires_at REAL NOT NULL,       -- When expires
    content_hash TEXT NOT NULL,     -- MD5 hash of content
    metadata TEXT NOT NULL,         -- JSON metadata
    access_count INTEGER DEFAULT 0, -- Number of accesses
    last_accessed REAL DEFAULT 0    -- Last access time
);
```

## Best Practices

### When to Use Caching
- **Static Content**: Documentation, API references, articles
- **Development**: Testing with the same URLs repeatedly
- **Bulk Processing**: Scraping multiple pages from the same site
- **Cost Optimization**: Reducing API credit usage

### When NOT to Use Caching
- **Real-time Data**: Stock prices, live scores, breaking news
- **Frequently Updated Content**: Social media feeds, dynamic dashboards
- **Time-sensitive Information**: Where freshness is critical

### Cache Duration Guidelines
- **Documentation**: 24-168 hours (1-7 days)
- **API References**: 24-72 hours (1-3 days)
- **News Articles**: 1-6 hours
- **Static Pages**: 168+ hours (7+ days)

## Performance Impact

### Benefits
- **Reduced API Costs**: Significant savings on repeated requests
- **Faster Response Times**: Cached content loads instantly
- **Reduced Network Usage**: Less bandwidth consumption
- **Improved Reliability**: Works offline for cached content

### Overhead
- **Storage Space**: Cache database grows over time
- **Initial Setup**: First request still requires API call
- **Memory Usage**: Minimal impact on application memory

## Troubleshooting

### Common Issues

#### Cache Not Working
1. Check if caching is enabled: `pdd firecrawl-cache info`
2. Verify environment variables are set correctly
3. Check cache directory permissions

#### High Storage Usage
1. Reduce `FIRECRAWL_CACHE_MAX_SIZE_MB`
2. Lower `FIRECRAWL_CACHE_MAX_ENTRIES`
3. Clear cache: `pdd firecrawl-cache clear`

#### Stale Content
1. Reduce `FIRECRAWL_CACHE_TTL_HOURS`
2. Clear specific entries or entire cache
3. Use `maxAge=0` in Firecrawl API calls for fresh content

### Debug Information

```bash
# View detailed cache statistics
pdd firecrawl-cache stats

# Check cache configuration
pdd firecrawl-cache info

# Test specific URL
pdd firecrawl-cache check --url https://example.com
```

## Implementation Details

### Architecture
- **Client-side Cache**: SQLite database for persistent storage
- **Server-side Cache**: Firecrawl's built-in caching via `maxAge` parameter
- **URL Normalization**: Consistent cache keys across requests
- **Automatic Cleanup**: Background maintenance of cache health

### Security Considerations
- Cache content is stored in plain text
- URLs are normalized but original URLs are preserved
- No authentication or encryption for cached data
- Consider cache location security for sensitive content

### Future Enhancements
- Compression for large cached content
- Cache warming strategies
- Distributed caching support
- Cache analytics and reporting
- Integration with other caching systems

## Related Issues

This implementation addresses:
- **Issue #46**: Cache firecrawl results so it doesn't use up the API credit

## Contributing

To contribute to the Firecrawl caching functionality:

1. Follow the existing code style and patterns
2. Add tests for new functionality
3. Update documentation for any changes
4. Consider backward compatibility
5. Test with various URL patterns and content types
