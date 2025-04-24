# Install with pip install firecrawl-py
from firecrawl import FirecrawlApp
import os

app = FirecrawlApp(api_key=os.environ.get('FIRECRAWL_API_KEY', 'YOUR_API_KEY'))


scrape_result = app.scrape_url('https://www.google.com', formats=['markdown'])
print(scrape_result.markdown)