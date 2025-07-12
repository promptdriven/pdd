import csv
import os
import re
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from pathlib import Path
from io import StringIO

# --- Configuration ---
CLAUDE_CSV_PATH = Path('analysis/claude_creation.csv')
PDD_CSV_PATH = Path('analysis/PDD_creation.csv')
OUTPUT_DIR = Path('creation_report')

# --- Helper Functions ---

def parse_duration_to_seconds(duration_str: str) -> float:
    """
    Converts a duration string (e.g., "1h 35m 33.0s", "35m 28.3s") to total seconds.
    Handles missing components (hours, minutes, or seconds).
    """
    if pd.isna(duration_str) or not isinstance(duration_str, str):
        return 0.0
    
    hours, minutes, seconds = 0, 0, 0.0
    
    h_match = re.search(r'(\d+)h', duration_str)
    if h_match:
        hours = int(h_match.group(1))
        
    m_match = re.search(r'(\d+)m', duration_str)
    if m_match:
        minutes = int(m_match.group(1))
        
    s_match = re.search(r'([\d\.]+)s', duration_str)
    if s_match:
        seconds = float(s_match.group(1))
        
    total_seconds = hours * 3600 + minutes * 60 + seconds
    return total_seconds

def format_seconds_to_hms(total_seconds: float) -> str:
    """
    Formats total seconds into a human-readable string "Xh Ym Z.Ws".
    """
    if pd.isna(total_seconds):
        return "N/A"
    
    s = total_seconds
    h = int(s // 3600)
    s %= 3600
    m = int(s // 60)
    s %= 60
    
    parts = []
    if h > 0:
        parts.append(f"{h}h")
    if m > 0:
        parts.append(f"{m}m")
    if s > 0 or not parts: # Always show seconds if no h or m, or if s > 0
        parts.append(f"{s:.1f}s")
        
    return " ".join(parts) if parts else "0.0s"

def load_and_preprocess_claude_data(csv_path: Path) -> pd.DataFrame | None:
    """Loads and preprocesses the Claude creation data."""
    print(f"Loading Claude data from: {csv_path}")
    try:
        # Use the provided CSV data for demonstration if actual file not found
        # This is for making the script runnable with the prompt's data
        if not csv_path.exists():
            print(f"Warning: File {csv_path} not found. Using example data from prompt.")
            claude_csv_content = """Total Cost,API Duration,Wall Duration,Lines Added,Lines Removed
$9.97,35m 28.3s,1h 35m 33.0s,4265,597
$10.46,40m 53.6s,1h 31m 13.2s,2011,498
$0.2631,1m 12.2s,3m 18.2s,4,4
$0.83,5m 52.4s,16m 3.8s,67,6
$7.01,39m 56.0s,2h 52m 47.2s,812,295
"""
            df_claude = pd.read_csv(StringIO(claude_csv_content), sep=',', quoting=csv.QUOTE_MINIMAL)
        else:
            df_claude = pd.read_csv(csv_path, sep=',', quoting=csv.QUOTE_MINIMAL)

    except FileNotFoundError:
        print(f"Error: Claude CSV file not found at {csv_path}")
        return None
    except Exception as e:
        print(f"Error loading Claude CSV: {e}")
        return None

    if df_claude.empty:
        print("Error: Claude CSV file is empty.")
        return None

    print("\nClaude data preview (raw):")
    print(df_claude.head())

    # Standardize column names
    df_claude.columns = [col.strip().replace(' ', '_').lower() for col in df_claude.columns]
    print("\nClaude columns (standardized):", df_claude.columns.tolist())

    # Verify required columns
    required_cols = ['total_cost', 'api_duration', 'wall_duration', 'lines_added', 'lines_removed']
    for col in required_cols:
        if col not in df_claude.columns:
            print(f"Error: Missing required column '{col}' in Claude data.")
            return None

    # Clean and convert 'total_cost'
    df_claude['total_cost'] = df_claude['total_cost'].replace({'\$': ''}, regex=True).astype(float)
    
    # Convert duration strings to seconds
    df_claude['api_duration_seconds'] = df_claude['api_duration'].apply(parse_duration_to_seconds)
    df_claude['wall_duration_seconds'] = df_claude['wall_duration'].apply(parse_duration_to_seconds)

    # Ensure 'lines_added' and 'lines_removed' are numeric
    df_claude['lines_added'] = pd.to_numeric(df_claude['lines_added'], errors='coerce').fillna(0).astype(int)
    df_claude['lines_removed'] = pd.to_numeric(df_claude['lines_removed'], errors='coerce').fillna(0).astype(int)


    print("\nClaude data preview (processed):")
    print(df_claude.head())
    print("\nClaude data types (processed):")
    print(df_claude.dtypes)
    
    return df_claude

def load_and_preprocess_pdd_data(csv_path: Path) -> pd.DataFrame | None:
    """Loads and preprocesses the PDD creation data."""
    print(f"\nLoading PDD data from: {csv_path}")
    try:
        # Use the provided CSV data for demonstration if actual file not found
        if not csv_path.exists():
            print(f"Warning: File {csv_path} not found. Using example data from prompt.")
            pdd_csv_content = """module,avg_time,total_time,avg_cost,total_cost
__init__,201.14583333333334,1206.875,0.2806173166666667,1.6837039000000003
anthropic_service,394.1295,2364.777,0.4338396916666667,2.60303815
caching_manager,131.4565,788.739,0.39087164166666666,2.34522985
cli,103.59766666666667,621.586,0.28302760833333335,1.69816565
config,268.2664285714286,1877.8650000000002,0.6513883928571429,4.55971875
cost_tracker,286.63933333333335,1719.8360000000002,0.3199597583333334,1.9197585500000003
edit_tool_impl,361.14799999999997,2166.888,0.5458140000000001,3.2748840000000006
file_handler,321.13228571428573,2247.926,0.5430141571428572,3.8010991
instruction_parser,286.99983333333336,1721.999,0.3802859916666666,2.2817159499999997
main_editor,1645.7278333333334,9874.367,0.5656376916666667,3.3938261499999998
prompts,109.875,659.25,0.2954146583333333,1.77248795
utils,51.00416666666666,306.025,0.09755935833333333,0.58535615
"""
            df_pdd = pd.read_csv(StringIO(pdd_csv_content), sep=',', quoting=csv.QUOTE_MINIMAL)
        else:
            df_pdd = pd.read_csv(csv_path, sep=',', quoting=csv.QUOTE_MINIMAL)

    except FileNotFoundError:
        print(f"Error: PDD CSV file not found at {csv_path}")
        return None
    except Exception as e:
        print(f"Error loading PDD CSV: {e}")
        return None

    if df_pdd.empty:
        print("Error: PDD CSV file is empty.")
        return None
        
    print("\nPDD data preview (raw):")
    print(df_pdd.head())
    print("\nPDD columns:", df_pdd.columns.tolist())

    # Verify required columns
    required_cols = ['module', 'avg_time', 'total_time', 'avg_cost', 'total_cost']
    for col in required_cols:
        if col not in df_pdd.columns:
            print(f"Error: Missing required column '{col}' in PDD data.")
            return None
            
    # Ensure numeric types (already float as per prompt, but good to verify)
    for col in ['avg_time', 'total_time', 'avg_cost', 'total_cost']:
        df_pdd[col] = pd.to_numeric(df_pdd[col], errors='coerce')
        if df_pdd[col].isnull().any():
            print(f"Warning: NaNs found in PDD column '{col}' after numeric conversion.")
            df_pdd[col] = df_pdd[col].fillna(0)


    print("\nPDD data preview (processed):")
    print(df_pdd.head())
    print("\nPDD data types (processed):")
    print(df_pdd.dtypes)

    return df_pdd

# --- Main Analysis Function ---
def perform_analysis():
    """Performs the comparative analysis and generates reports."""
    
    # Create output directory
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    print(f"\nOutput will be saved to: {OUTPUT_DIR}")

    # Load data
    df_claude = load_and_preprocess_claude_data(CLAUDE_CSV_PATH)
    df_pdd = load_and_preprocess_pdd_data(PDD_CSV_PATH)

    if df_claude is None or df_pdd is None:
        print("\nExiting due to data loading errors.")
        return

    # Initialize markdown report content
    report_md = f"# Comparative Analysis: Claude vs. PDD Creation Task\n\n"
    report_md += f"Analysis based on data from `{CLAUDE_CSV_PATH.name}` and `{PDD_CSV_PATH.name}`.\n\n"

    # --- Cost Analysis ---
    print("\n--- Cost Analysis ---")
    report_md += "## 1. Cost Analysis\n\n"

    # Claude Cost
    claude_total_cost = df_claude['total_cost'].sum()
    claude_avg_cost_per_run = df_claude['total_cost'].mean()
    claude_num_runs = len(df_claude)
    print(f"Claude - Total Cost: ${claude_total_cost:.2f}")
    print(f"Claude - Number of Runs: {claude_num_runs}")
    print(f"Claude - Average Cost per Run: ${claude_avg_cost_per_run:.2f}")

    report_md += "### 1.1. Claude Creation\n"
    report_md += f"- Total Cost: ${claude_total_cost:.2f}\n"
    report_md += f"- Number of Runs: {claude_num_runs}\n"
    report_md += f"- Average Cost per Run: ${claude_avg_cost_per_run:.2f}\n"
    report_md += f"- Cost per Run Statistics:\n{df_claude['total_cost'].describe().to_markdown()}\n\n"

    fig, ax = plt.subplots(figsize=(8, 5))
    sns.boxplot(x=df_claude['total_cost'], ax=ax)
    ax.set_title('Claude: Cost per Run Distribution')
    ax.set_xlabel('Cost per Run ($)')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'claude_cost_per_run_dist.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![Claude Cost per Run Distribution]({plot_path.name})\n\n"

    # PDD Cost
    pdd_total_cost = df_pdd['total_cost'].sum()
    pdd_avg_cost_per_module = df_pdd['avg_cost'].mean() # Mean of 'avg_cost' column
    pdd_num_modules = len(df_pdd)
    print(f"PDD - Total Cost: ${pdd_total_cost:.2f}")
    print(f"PDD - Number of Modules: {pdd_num_modules}")
    print(f"PDD - Overall Average Cost per Module (from 'avg_cost'): ${pdd_avg_cost_per_module:.2f}")
    
    report_md += "### 1.2. PDD Creation\n"
    report_md += f"- Total Cost (sum of module total_costs): ${pdd_total_cost:.2f}\n"
    report_md += f"- Number of Modules: {pdd_num_modules}\n"
    report_md += f"- Overall Average Cost per Module (mean of 'avg_cost' column): ${pdd_avg_cost_per_module:.2f}\n"
    report_md += f"- 'avg_cost' per Module Statistics:\n{df_pdd['avg_cost'].describe().to_markdown()}\n\n"
    report_md += f"- 'total_cost' per Module Statistics:\n{df_pdd['total_cost'].describe().to_markdown()}\n\n"


    fig, ax = plt.subplots(figsize=(8, 5))
    sns.boxplot(x=df_pdd['avg_cost'], ax=ax)
    ax.set_title('PDD: Average Cost per Module Distribution')
    ax.set_xlabel('Average Cost per Module ($)')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'pdd_avg_cost_per_module_dist.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![PDD Average Cost per Module Distribution]({plot_path.name})\n\n"

    # PDD Top N modules by cost
    pdd_top_cost_modules = df_pdd.sort_values(by='total_cost', ascending=False).head(10)
    report_md += "Top 10 PDD Modules by Total Cost:\n"
    report_md += f"{pdd_top_cost_modules[['module', 'total_cost']].to_markdown(index=False)}\n\n"
    
    fig, ax = plt.subplots(figsize=(12, 7))
    sns.barplot(data=pdd_top_cost_modules, x='total_cost', y='module', ax=ax, palette="viridis")
    ax.set_title('PDD: Top 10 Modules by Total Cost')
    ax.set_xlabel('Total Cost ($)')
    ax.set_ylabel('Module')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'pdd_top_modules_by_cost.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![PDD Top Modules by Cost]({plot_path.name})\n\n"


    # Cost Comparison
    report_md += "### 1.3. Cost Comparison Summary\n"
    cost_comp_data = {
        'Metric': ['Total Cost', 'Average Cost per Unit'],
        'Claude': [f"${claude_total_cost:.2f}", f"${claude_avg_cost_per_run:.2f} (per run)"],
        'PDD': [f"${pdd_total_cost:.2f}", f"${pdd_avg_cost_per_module:.2f} (avg per module)"]
    }
    cost_comp_df = pd.DataFrame(cost_comp_data)
    report_md += cost_comp_df.to_markdown(index=False) + "\n\n"

    fig, ax = plt.subplots(figsize=(8, 5))
    sns.barplot(x=['Claude (All Runs)', 'PDD (All Modules)'], y=[claude_total_cost, pdd_total_cost], ax=ax, palette="mako")
    ax.set_title('Total Cost Comparison')
    ax.set_ylabel('Total Cost ($)')
    for i, v in enumerate([claude_total_cost, pdd_total_cost]):
        ax.text(i, v + 0.01 * max(claude_total_cost, pdd_total_cost), f"${v:.2f}", ha='center', va='bottom')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'total_cost_comparison.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![Total Cost Comparison]({plot_path.name})\n\n"


    # --- Time Analysis (Wall Duration / Total Time) ---
    print("\n--- Time Analysis ---")
    report_md += "## 2. Time Analysis (Wall Duration / Total Time)\n\n"

    # Claude Time
    claude_total_wall_duration_s = df_claude['wall_duration_seconds'].sum()
    claude_avg_wall_duration_s = df_claude['wall_duration_seconds'].mean()
    print(f"Claude - Total Wall Duration: {format_seconds_to_hms(claude_total_wall_duration_s)} ({claude_total_wall_duration_s:.2f}s)")
    print(f"Claude - Average Wall Duration per Run: {format_seconds_to_hms(claude_avg_wall_duration_s)} ({claude_avg_wall_duration_s:.2f}s)")
    
    report_md += "### 2.1. Claude Creation (Wall Duration)\n"
    report_md += f"- Total Wall Duration: {format_seconds_to_hms(claude_total_wall_duration_s)} ({claude_total_wall_duration_s:.2f} seconds)\n"
    report_md += f"- Wall Duration per Run Statistics (seconds):\n{df_claude['wall_duration_seconds'].describe().to_markdown()}\n\n"

    fig, ax = plt.subplots(figsize=(8, 5))
    sns.boxplot(x=df_claude['wall_duration_seconds'], ax=ax)
    ax.set_title('Claude: Wall Duration per Run Distribution')
    ax.set_xlabel('Wall Duration per Run (seconds)')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'claude_wall_duration_dist.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![Claude Wall Duration Distribution]({plot_path.name})\n\n"

    # Claude API Duration (for completeness, not direct comparison)
    claude_total_api_duration_s = df_claude['api_duration_seconds'].sum()
    claude_avg_api_duration_s = df_claude['api_duration_seconds'].mean()
    report_md += "Claude API Duration (for context):\n"
    report_md += f"- Total API Duration: {format_seconds_to_hms(claude_total_api_duration_s)} ({claude_total_api_duration_s:.2f} seconds)\n"
    report_md += f"- API Duration per Run Statistics (seconds):\n{df_claude['api_duration_seconds'].describe().to_markdown()}\n\n"


    # PDD Time
    pdd_total_time_s = df_pdd['total_time'].sum() # Sum of 'total_time' for all modules
    pdd_avg_module_total_time_s = df_pdd['total_time'].mean() # Avg of 'total_time' across modules
    print(f"PDD - Total Time (sum of module total_times): {format_seconds_to_hms(pdd_total_time_s)} ({pdd_total_time_s:.2f}s)")
    print(f"PDD - Average 'total_time' per Module: {format_seconds_to_hms(pdd_avg_module_total_time_s)} ({pdd_avg_module_total_time_s:.2f}s)")

    report_md += "### 2.2. PDD Creation (Total Time per Module)\n"
    report_md += f"- Total Time (sum of module `total_time`): {format_seconds_to_hms(pdd_total_time_s)} ({pdd_total_time_s:.2f} seconds)\n"
    report_md += f"- `total_time` per Module Statistics (seconds):\n{df_pdd['total_time'].describe().to_markdown()}\n\n"

    fig, ax = plt.subplots(figsize=(8, 5))
    sns.boxplot(x=df_pdd['total_time'], ax=ax)
    ax.set_title('PDD: Total Time per Module Distribution')
    ax.set_xlabel('Total Time per Module (seconds)')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'pdd_total_time_per_module_dist.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![PDD Total Time per Module Distribution]({plot_path.name})\n\n"

    # PDD Top N modules by time
    pdd_top_time_modules = df_pdd.sort_values(by='total_time', ascending=False).head(10)
    report_md += "Top 10 PDD Modules by Total Time:\n"
    report_md += f"{pdd_top_time_modules[['module', 'total_time']].to_markdown(index=False)}\n\n"

    fig, ax = plt.subplots(figsize=(12, 7))
    sns.barplot(data=pdd_top_time_modules, x='total_time', y='module', ax=ax, palette="crest")
    ax.set_title('PDD: Top 10 Modules by Total Time')
    ax.set_xlabel('Total Time (seconds)')
    ax.set_ylabel('Module')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'pdd_top_modules_by_time.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![PDD Top Modules by Time]({plot_path.name})\n\n"

    # Time Comparison
    report_md += "### 2.3. Time Comparison Summary\n"
    time_comp_data = {
        'Metric': ['Total Execution Time', 'Average Time per Unit'],
        'Claude': [f"{format_seconds_to_hms(claude_total_wall_duration_s)}", f"{format_seconds_to_hms(claude_avg_wall_duration_s)} (per run, wall duration)"],
        'PDD': [f"{format_seconds_to_hms(pdd_total_time_s)}", f"{format_seconds_to_hms(pdd_avg_module_total_time_s)} (avg module total_time)"]
    }
    time_comp_df = pd.DataFrame(time_comp_data)
    report_md += time_comp_df.to_markdown(index=False) + "\n\n"

    fig, ax = plt.subplots(figsize=(8, 5))
    sns.barplot(x=['Claude (Wall Duration)', 'PDD (Total Time)'], y=[claude_total_wall_duration_s, pdd_total_time_s], ax=ax, palette="flare")
    ax.set_title('Total Execution Time Comparison')
    ax.set_ylabel('Total Time (seconds)')
    for i, v in enumerate([claude_total_wall_duration_s, pdd_total_time_s]):
        ax.text(i, v + 0.01 * max(claude_total_wall_duration_s, pdd_total_time_s), f"{format_seconds_to_hms(v)}", ha='center', va='bottom')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'total_time_comparison.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![Total Time Comparison]({plot_path.name})\n\n"

    # --- Lines Added/Removed Analysis (Claude Only) ---
    print("\n--- Lines Added/Removed Analysis (Claude Only) ---")
    report_md += "## 3. Lines Added/Removed Analysis (Claude Only)\n\n"
    
    claude_total_lines_added = df_claude['lines_added'].sum()
    claude_total_lines_removed = df_claude['lines_removed'].sum()
    claude_avg_lines_added = df_claude['lines_added'].mean()
    claude_avg_lines_removed = df_claude['lines_removed'].mean()
    claude_net_lines_added_total = claude_total_lines_added - claude_total_lines_removed
    df_claude['net_lines_added'] = df_claude['lines_added'] - df_claude['lines_removed']
    claude_avg_net_lines_added = df_claude['net_lines_added'].mean()

    print(f"Claude - Total Lines Added: {claude_total_lines_added}")
    print(f"Claude - Total Lines Removed: {claude_total_lines_removed}")
    print(f"Claude - Net Lines Added (Total): {claude_net_lines_added_total}")
    print(f"Claude - Average Lines Added per Run: {claude_avg_lines_added:.2f}")
    print(f"Claude - Average Lines Removed per Run: {claude_avg_lines_removed:.2f}")
    print(f"Claude - Average Net Lines Added per Run: {claude_avg_net_lines_added:.2f}")

    report_md += f"- Total Lines Added: {claude_total_lines_added}\n"
    report_md += f"- Total Lines Removed: {claude_total_lines_removed}\n"
    report_md += f"- Net Lines Added (Total): {claude_net_lines_added_total}\n"
    report_md += f"- Lines Added per Run Statistics:\n{df_claude['lines_added'].describe().to_markdown()}\n\n"
    report_md += f"- Lines Removed per Run Statistics:\n{df_claude['lines_removed'].describe().to_markdown()}\n\n"
    report_md += f"- Net Lines Added per Run Statistics:\n{df_claude['net_lines_added'].describe().to_markdown()}\n\n"

    fig, axes = plt.subplots(1, 2, figsize=(15, 6))
    sns.histplot(df_claude['lines_added'], ax=axes[0], kde=True, color='skyblue')
    axes[0].set_title('Claude: Distribution of Lines Added per Run')
    axes[0].set_xlabel('Lines Added')
    sns.histplot(df_claude['lines_removed'], ax=axes[1], kde=True, color='salmon')
    axes[1].set_title('Claude: Distribution of Lines Removed per Run')
    axes[1].set_xlabel('Lines Removed')
    plt.tight_layout()
    plot_path = OUTPUT_DIR / 'claude_lines_added_removed_dist.png'
    fig.savefig(plot_path)
    plt.close(fig)
    report_md += f"![Claude Lines Added/Removed Distribution]({plot_path.name})\n\n"


    # --- Summary and Insights ---
    print("\n--- Summary and Insights ---")
    report_md += "## 4. Summary and Insights\n\n"

    report_md += "This analysis compared file creation tasks using two approaches, reflected in `claude_creation.csv` (multiple runs) and `PDD_creation.csv` (single process, module breakdown).\n\n"

    report_md += "**Key Cost Observations:**\n"
    report_md += f"- The total cost for all Claude runs was ${claude_total_cost:.2f} over {claude_num_runs} runs, averaging ${claude_avg_cost_per_run:.2f} per run.\n"
    report_md += f"- The PDD process had a total cost of ${pdd_total_cost:.2f}, distributed across {pdd_num_modules} modules. The overall average cost per module (from 'avg_cost') was ${pdd_avg_cost_per_module:.2f}.\n"
    if claude_total_cost > pdd_total_cost:
        report_md += "- PDD appears more cost-effective in total for the tasks represented in these datasets.\n"
    elif pdd_total_cost > claude_total_cost:
        report_md += "- Claude (sum of runs) appears more cost-effective in total for the tasks represented.\n"
    else:
        report_md += "- The total costs are comparable.\n"
    report_md += "- Note: Claude data represents multiple, possibly distinct, creation tasks, while PDD data is a breakdown of one larger process. Direct cost-per-task comparison is nuanced.\n\n"

    report_md += "**Key Time Observations (Wall/Total Time):**\n"
    report_md += f"- Claude runs had a total wall duration of {format_seconds_to_hms(claude_total_wall_duration_s)}, with an average of {format_seconds_to_hms(claude_avg_wall_duration_s)} per run.\n"
    report_md += f"- The PDD process had a total execution time of {format_seconds_to_hms(pdd_total_time_s)} (sum of module `total_time`).\n"
    if claude_total_wall_duration_s > pdd_total_time_s:
        report_md += "- PDD was faster in total execution time compared to the sum of Claude's wall durations.\n"
    elif pdd_total_time_s > claude_total_wall_duration_s:
        report_md += "- Claude (sum of wall durations) was faster in total execution time compared to PDD.\n"
    else:
        report_md += "- The total execution times are comparable.\n"
    report_md += "- PDD's `main_editor` module was a significant contributor to its total time and cost. Optimizing such modules could yield substantial improvements.\n\n"
    
    report_md += "**Nature of Data:**\n"
    report_md += "- It's crucial to remember that Claude's data represents multiple independent runs, potentially for different specific creation tasks. PDD's data is a breakdown of a single, possibly more complex, integrated process.\n"
    report_md += "- This difference means that 'total' figures for Claude are aggregates of separate events, while for PDD, they represent components of one event.\n\n"

    report_md += "**Potential Insights & Recommendations:**\n"
    report_md += "- **PDD Efficiency:** For PDD, analyzing modules with high `total_time` and `total_cost` (e.g., `main_editor`, `file_handler`, `edit_tool_impl`) can identify bottlenecks for optimization.\n"
    report_md += "- **Claude Variability:** The distribution of costs and times for Claude runs (if tasks were similar) can indicate variability in performance. If tasks were diverse, it reflects the cost/time for different types of creation jobs.\n"
    report_md += "- **Cost vs. Time Trade-off:** The data can be used to explore cost vs. time trade-offs. For example, PDD's `anthropic_service` has a relatively high average cost but its total time contribution might be justified if it performs critical, complex tasks efficiently.\n"
    report_md += "- **Further Analysis:** If the Claude runs correspond to specific types of files or tasks, segmenting the Claude data by these types could provide more granular insights into its performance characteristics.\n\n"

    # Save Markdown report
    report_file_path = OUTPUT_DIR / 'creation_analysis_report.md'
    with open(report_file_path, 'w') as f:
        f.write(report_md)
    print(f"\nAnalysis complete. Report saved to: {report_file_path}")


if __name__ == "__main__":
    # Set plot style
    sns.set_style("whitegrid")
    plt.rcParams['figure.dpi'] = 100 # Adjust for higher quality plots if needed

    # Create dummy analysis directory and files if they don't exist, for standalone running
    # This part is for demonstration; in a real scenario, these files would exist.
    if not CLAUDE_CSV_PATH.parent.exists():
        CLAUDE_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    if not PDD_CSV_PATH.parent.exists(): # Should be same as Claude's parent
        PDD_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)

    # The load_and_preprocess functions now handle using example data if files are not found.
    # So, explicit creation of dummy files here is not strictly necessary for the script to run.
    # However, if you want to test with actual files, create them with the content below:
    
    # Example: Create dummy claude_creation.csv if it doesn't exist
#     if not CLAUDE_CSV_PATH.exists():
#         claude_csv_content = """Total Cost,API Duration,Wall Duration,Lines Added,Lines Removed
# $9.97,35m 28.3s,1h 35m 33.0s,4265,597
# $10.46,40m 53.6s,1h 31m 13.2s,2011,498
# $0.2631,1m 12.2s,3m 18.2s,4,4
# $0.83,5m 52.4s,16m 3.8s,67,6
# $7.01,39m 56.0s,2h 52m 47.2s,812,295
# """
#         with open(CLAUDE_CSV_PATH, 'w') as f:
#             f.write(claude_csv_content)
#         print(f"Created dummy {CLAUDE_CSV_PATH}")

    # Example: Create dummy PDD_creation.csv if it doesn't exist
#     if not PDD_CSV_PATH.exists():
#         pdd_csv_content = """module,avg_time,total_time,avg_cost,total_cost
# __init__,201.14583333333334,1206.875,0.2806173166666667,1.6837039000000003
# anthropic_service,394.1295,2364.777,0.4338396916666667,2.60303815
# caching_manager,131.4565,788.739,0.39087164166666666,2.34522985
# cli,103.59766666666667,621.586,0.28302760833333335,1.69816565
# config,268.2664285714286,1877.8650000000002,0.6513883928571429,4.55971875
# cost_tracker,286.63933333333335,1719.8360000000002,0.3199597583333334,1.9197585500000003
# edit_tool_impl,361.14799999999997,2166.888,0.5458140000000001,3.2748840000000006
# file_handler,321.13228571428573,2247.926,0.5430141571428572,3.8010991
# instruction_parser,286.99983333333336,1721.999,0.3802859916666666,2.2817159499999997
# main_editor,1645.7278333333334,9874.367,0.5656376916666667,3.3938261499999998
# prompts,109.875,659.25,0.2954146583333333,1.77248795
# utils,51.00416666666666,306.025,0.09755935833333333,0.58535615
# """
#         with open(PDD_CSV_PATH, 'w') as f:
#             f.write(pdd_csv_content)
#         print(f"Created dummy {PDD_CSV_PATH}")

    perform_analysis()
