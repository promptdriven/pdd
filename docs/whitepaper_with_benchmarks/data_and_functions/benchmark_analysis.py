import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.figure
import seaborn as sns
from scipy import stats
import statsmodels.stats.proportion as smp
import os
from typing import List, Tuple, Optional, Dict, Any

# --- Configuration ---
CLAUDE_RESULTS_PATH = 'analysis/claude_results.csv'
PDD_RESULTS_PATH = 'analysis/PDD_results.csv'
OUTPUT_SUBDIR = 'analysis_report' # Subdirectory within 'analysis/'
OUTPUT_DIR = os.path.join('analysis', OUTPUT_SUBDIR)

# Weights for overall score
W_TIME = 0.3
W_COST = 0.3
W_SUCCESS = 0.4

# --- Helper Functions ---

def create_output_directory() -> None:
    """Creates the output directory if it doesn't exist."""
    if not os.path.exists(OUTPUT_DIR):
        os.makedirs(OUTPUT_DIR)
        print(f"Created directory: {OUTPUT_DIR}")

def save_plot(fig: matplotlib.figure.Figure, filename: str, tight_layout: bool = True) -> str:
    """Saves the given matplotlib figure to the output directory."""
    if tight_layout:
        fig.tight_layout()
    path = os.path.join(OUTPUT_DIR, filename)
    fig.savefig(path)
    plt.close(fig)
    return path

def min_max_normalize(series: pd.Series, lower_is_better: bool = True) -> pd.Series:
    """Normalizes a pandas Series using min-max scaling."""
    min_val = series.min()
    max_val = series.max()
    if max_val == min_val: # Avoid division by zero if all values are the same
        return pd.Series(0.5, index=series.index) # Neutral score if no variance
    
    normalized = (series - min_val) / (max_val - min_val)
    if lower_is_better:
        return 1 - normalized
    return normalized

def calculate_rank_biserial(U: float, n1: int, n2: int) -> float:
    """Calculates rank-biserial correlation from Mann-Whitney U."""
    # Common formula: r = 1 - (2U / (n1 * n2))
    # U here should be the U statistic for the group that would be expected to have smaller sum of ranks if H0 is false
    # Or, more simply, use the smaller of U1 and U2.
    # scipy.stats.mannwhitneyu returns one U value (typically U2).
    # The formula r = 1 - (2 * U_scipy) / (n1 * n2) is equivalent to (U1 - U2) / (n1 * n2)
    # where U_scipy is the U value returned by scipy.
    if n1 * n2 == 0: return 0.0 # Avoid division by zero if either group is empty
    return 1 - (2 * U) / (n1 * n2)


def calculate_cramers_v(chi2: float, n: int, contingency_table: pd.DataFrame) -> float:
    """Calculates Cramér's V from Chi-squared test."""
    if n == 0: return 0.0
    phi2 = chi2 / n
    k, r = contingency_table.shape
    if min(k-1, r-1) == 0: return 0.0 # Avoid division by zero
    return np.sqrt(phi2 / min(k - 1, r - 1))

# --- Main Analysis Functions ---

def load_and_prepare_data() -> Optional[pd.DataFrame]:
    """Loads and prepares the benchmark data."""
    try:
        claude_df = pd.read_csv(CLAUDE_RESULTS_PATH)
        pdd_df = pd.read_csv(PDD_RESULTS_PATH)
    except FileNotFoundError as e:
        print(f"Error: Input CSV file not found. {e}")
        print("Please ensure 'analysis/claude_results.csv' and 'analysis/PDD_results.csv' exist.")
        return None

    claude_df['tool'] = 'Claude'
    pdd_df['tool'] = 'PDD'
    
    combined_df = pd.concat([claude_df, pdd_df], ignore_index=True)
    
    # Ensure numeric types for relevant columns
    for col in ['execution_time_seconds', 'api_cost', 'success']:
        combined_df[col] = pd.to_numeric(combined_df[col], errors='coerce')
    
    # Handle potential NaNs from coercion or in data
    combined_df.dropna(subset=['execution_time_seconds', 'api_cost', 'success'], inplace=True)
    
    return combined_df

def overall_performance_analysis(df: pd.DataFrame) -> Tuple[List[str], pd.DataFrame]:
    """Performs overall performance comparison."""
    report_parts: List[str] = ["## 1. Overall Performance Comparison\n"]
    
    overall_stats = df.groupby('tool').agg(
        avg_execution_time=('execution_time_seconds', 'mean'),
        avg_api_cost=('api_cost', 'mean'),
        success_rate=('success', 'mean'),
        total_tasks=('success', 'count')
    ).reset_index()

    report_parts.append("### Key Metrics\n")
    report_parts.append(overall_stats.to_markdown(index=False) + "\n")

    # Bar charts
    metrics_to_plot: Dict[str, str] = {
        'avg_execution_time': 'Average Execution Time (s)',
        'avg_api_cost': 'Average API Cost ($)',
        'success_rate': 'Success Rate'
    }
    for metric, title in metrics_to_plot.items():
        fig, ax = plt.subplots()
        
        plot_data = overall_stats
        y_label = title

        if "time" in metric:
            y_label = "Average Execution Time (seconds)"
        elif "cost" in metric:
            y_label = "Average API Cost (dollars)"
        elif "success" in metric:
            y_label = "Success Rate (%)"
            plot_data = overall_stats.copy()
            plot_data[metric] = plot_data[metric] * 100
        
        sns.barplot(x='tool', y=metric, data=plot_data, ax=ax)
        ax.set_title(title)
        ax.set_xlabel("Tool")
        ax.set_ylabel(y_label)
        img_path = save_plot(fig, f"overall_{metric}.png")
        report_parts.append(f"![{title}]({os.path.basename(img_path)})\n")

    # Weighted Scoring
    report_parts.append("\n### Weighted Scoring for Best Overall Tool\n")
    report_parts.append(f"The best overall tool is determined using a weighted scoring system. The formula is: \n`Overall Score = {W_TIME} * norm_time + {W_COST} * norm_cost + {W_SUCCESS} * norm_success_rate`\n")
    report_parts.append("Time and cost are normalized using min-max scaling (lower is better, hence `norm_time` and `norm_cost` are already inverted if needed). Success rate is already a [0, 1] metric (higher is better).\n")

    # Normalize across both tools for fair comparison
    all_avg_times = overall_stats['avg_execution_time']
    all_avg_costs = overall_stats['avg_api_cost']

    overall_stats['norm_time'] = min_max_normalize(all_avg_times, lower_is_better=True) 
    overall_stats['norm_cost'] = min_max_normalize(all_avg_costs, lower_is_better=True)
    # Success rate is already normalized (0-1), and higher is better.
    overall_stats['norm_success_rate'] = overall_stats['success_rate'] 

    overall_stats['overall_score'] = (
        W_TIME * overall_stats['norm_time'] +
        W_COST * overall_stats['norm_cost'] +
        W_SUCCESS * overall_stats['norm_success_rate']
    )
    
    report_parts.append("#### Calculated Scores:\n")
    report_parts.append(overall_stats[['tool', 'norm_time', 'norm_cost', 'norm_success_rate', 'overall_score']].to_markdown(index=False) + "\n")

    best_tool = overall_stats.loc[overall_stats['overall_score'].idxmax()]
    report_parts.append(f"\n**Best Overall Tool (based on weighted score): {best_tool['tool']}** with a score of {best_tool['overall_score']:.3f}\n")
    
    return report_parts, overall_stats


def dimension_specific_analysis(df: pd.DataFrame) -> List[str]:
    """Performs dimension-specific analysis."""
    report_parts: List[str] = ["\n## 2. Dimension-Specific Analysis\n"]
    dimensions: List[str] = ['file_size', 'language', 'edit_type']
    
    for dim in dimensions:
        report_parts.append(f"### Performance by {dim.replace('_', ' ').title()}\n")
        
        dim_stats = df.groupby(['tool', dim]).agg(
            avg_execution_time=('execution_time_seconds', 'mean'),
            avg_api_cost=('api_cost', 'mean'),
            success_rate=('success', 'mean')
        ).reset_index()
        
        report_parts.append(dim_stats.to_markdown(index=False) + "\n")

        # Grouped bar charts
        metrics_to_plot: Dict[str, str] = {
            'avg_execution_time': f'Average Execution Time by {dim}',
            'avg_api_cost': f'Average API Cost by {dim}',
            'success_rate': f'Success Rate by {dim}'
        }
        for metric, title in metrics_to_plot.items():
            fig, ax = plt.subplots(figsize=(10, 6))
            
            plot_data = dim_stats
            y_label = metric

            if "time" in metric:
                y_label = "Average Execution Time (seconds)"
            elif "cost" in metric:
                y_label = "Average API Cost (dollars)"
            elif "success" in metric:
                y_label = "Success Rate (%)"
                plot_data = dim_stats.copy()
                plot_data[metric] = plot_data[metric] * 100

            sns.barplot(x=dim, y=metric, hue='tool', data=plot_data, ax=ax)
            ax.set_title(title)
            ax.set_xlabel(dim.replace('_', ' ').title())
            ax.set_ylabel(y_label)
            img_path = save_plot(fig, f"{metric}_by_{dim}.png")
            report_parts.append(f"![{title}]({os.path.basename(img_path)})\n")
            
    return report_parts

def cost_efficiency_analysis(df: pd.DataFrame) -> List[str]:
    """Performs cost-efficiency analysis."""
    report_parts: List[str] = ["\n## 3. Cost-Efficiency Analysis\n"]

    # Cost per successful task
    total_costs = df.groupby('tool')['api_cost'].sum()
    successful_tasks = df[df['success'] == 1].groupby('tool')['success'].count()
    
    cost_efficiency = pd.DataFrame({
        'total_api_cost': total_costs,
        'num_successful_tasks': successful_tasks
    })
    # Ensure num_successful_tasks is present for all tools, fill with 0 if no successful tasks
    cost_efficiency = cost_efficiency.reindex(df['tool'].unique(), fill_value=0)
    cost_efficiency['cost_per_successful_task'] = np.where(
        cost_efficiency['num_successful_tasks'] > 0,
        cost_efficiency['total_api_cost'] / cost_efficiency['num_successful_tasks'],
        np.nan # Or 0, or some other indicator for no successful tasks
    )
    cost_efficiency = cost_efficiency.reset_index().rename(columns={'index': 'tool'})

    report_parts.append("### Cost Per Successful Task\n")
    report_parts.append(cost_efficiency.to_markdown(index=False) + "\n")

    fig, ax = plt.subplots()
    sns.barplot(x='tool', y='cost_per_successful_task', data=cost_efficiency, ax=ax)
    ax.set_title('Cost Per Successful Task')
    ax.set_ylabel('Cost Per Successful Task (dollars)')
    img_path = save_plot(fig, "cost_per_successful_task.png")
    report_parts.append(f"![Cost Per Successful Task]({os.path.basename(img_path)})\n")

    # Scatter plot: execution_time vs. api_cost
    fig, ax = plt.subplots(figsize=(10, 6))
    sns.scatterplot(x='execution_time_seconds', y='api_cost', hue='tool', data=df, alpha=0.6, ax=ax)
    ax.set_title('Execution Time vs. API Cost')
    ax.set_xlabel('Execution Time (seconds)')
    ax.set_ylabel('API Cost (dollars)')
    img_path = save_plot(fig, "time_vs_cost_scatter.png")
    report_parts.append(f"![Time vs. Cost Scatter Plot]({os.path.basename(img_path)})\n")

    # Bar chart for total API cost (Required Visualizations #6)
    fig, ax = plt.subplots()
    sns.barplot(x='tool', y='total_api_cost', data=cost_efficiency, ax=ax) # Re-using cost_efficiency df
    ax.set_title('Total API Cost for All Benchmarks')
    ax.set_ylabel('Total API Cost (dollars)')
    img_path = save_plot(fig, "total_api_cost_comparison.png")
    report_parts.append(f"![Total API Cost Comparison]({os.path.basename(img_path)})\n")
    
    return report_parts

def success_and_error_analysis(df: pd.DataFrame, overall_stats: pd.DataFrame) -> Tuple[List[str], pd.DataFrame]:
    """Performs success and error analysis."""
    report_parts: List[str] = ["\n## 4. Success and Error Analysis\n"]

    # Success rates across dimensions (already plotted in dimension_specific_analysis)
    report_parts.append("Success rates across dimensions are visualized in Section 2.\n")

    # Error message analysis
    failed_tasks = df[df['success'] == 0]
    if 'error_message' in failed_tasks.columns:
        error_summary = failed_tasks.groupby(['tool', 'error_message']).size().reset_index(name='count').sort_values(by=['tool', 'count'], ascending=[True, False])
        report_parts.append("### Common Error Messages for Failed Tasks\n")
        for tool in df['tool'].unique():
            report_parts.append(f"#### {tool}:\n")
            tool_errors = error_summary[error_summary['tool'] == tool]
            if not tool_errors.empty:
                report_parts.append(tool_errors[['error_message', 'count']].to_markdown(index=False) + "\n")
            else:
                report_parts.append("No failed tasks recorded for this tool or error messages not available.\n")
    else:
        report_parts.append("### Common Error Messages for Failed Tasks\n")
        report_parts.append("Column 'error_message' not found in the data for failed tasks.\n")

    # Confidence intervals for overall success rates
    report_parts.append("### Overall Success Rate Confidence Intervals (95%)\n")
    ci_data: List[Dict[str, Any]] = []
    for tool_name in overall_stats['tool'].unique():
        tool_data = overall_stats[overall_stats['tool'] == tool_name].iloc[0]
        n_success = int(tool_data['success_rate'] * tool_data['total_tasks'])
        n_total = int(tool_data['total_tasks'])
        if n_total > 0:
            ci_low, ci_upp = smp.proportion_confint(n_success, n_total, method='wilson')
            ci_data.append({'tool': tool_name, 'success_rate': tool_data['success_rate'], 'ci_lower': ci_low, 'ci_upper': ci_upp})
        else:
            ci_data.append({'tool': tool_name, 'success_rate': np.nan, 'ci_lower': np.nan, 'ci_upper': np.nan})
            
    ci_df = pd.DataFrame(ci_data)
    report_parts.append(ci_df.to_markdown(index=False) + "\n")
    
    return report_parts, ci_df


def statistical_significance_analysis(df: pd.DataFrame) -> Tuple[List[str], pd.DataFrame]:
    """Performs statistical significance tests."""
    report_parts: List[str] = ["\n## 5. Statistical Significance Analysis\n"]
    stat_results: List[Dict[str, Any]] = []

    pdd_data = df[df['tool'] == 'PDD']
    claude_data = df[df['tool'] == 'Claude']

    # Mann-Whitney U for continuous metrics
    for metric in ['execution_time_seconds', 'api_cost']:
        pdd_metric_data = pdd_data[metric].dropna()
        claude_metric_data = claude_data[metric].dropna()
        
        if pdd_metric_data.empty or claude_metric_data.empty:
            report_parts.append(f"Skipping {metric} due to empty data for one or both tools after dropping NaNs.\n")
            stat_results.append({'Metric': metric, 'Test': 'Mann-Whitney U', 'p-value': 'N/A', 'Effect Size (RBC)': 'N/A', 'Significance': 'N/A'})
            continue

        mwu_stat, p_value = stats.mannwhitneyu(pdd_metric_data, claude_metric_data, alternative='two-sided')
        
        n1, n2 = len(pdd_metric_data), len(claude_metric_data)
        rbc_val = calculate_rank_biserial(mwu_stat, n1, n2)
        rbc_str = f"{rbc_val:.3f}"

        significance = "Yes" if p_value < 0.05 else "No"
        stat_results.append({'Metric': metric, 'Test': 'Mann-Whitney U', 'p-value': f"{p_value:.3g}", 'Effect Size (RBC)': rbc_str, 'Significance': significance})

    # Chi-squared for success metric
    if not pdd_data.empty and not claude_data.empty:
        contingency_table = pd.crosstab(df['tool'], df['success'])
        if contingency_table.shape == (2,2) and contingency_table.values.min() > 0 : # Check if table is 2x2 and has counts > 0
            chi2, p_value, _, _ = stats.chi2_contingency(contingency_table)
            
            n_total = contingency_table.sum().sum()
            cramers_v = calculate_cramers_v(chi2, n_total, contingency_table)
            cramers_v_str = f"{cramers_v:.3f}"
            significance = "Yes" if p_value < 0.05 else "No"
        else:
            p_value = 1.0 # Not applicable
            cramers_v_str = "N/A"
            significance = "N/A (contingency table not 2x2 or has zero/low counts)"
            
        stat_results.append({'Metric': 'success', 'Test': 'Chi-squared', 'p-value': f"{p_value:.3g}", "Effect Size (Cramér's V)": cramers_v_str, 'Significance': significance})
    else:
        stat_results.append({'Metric': 'success', 'Test': 'Chi-squared', 'p-value': 'N/A', "Effect Size (Cramér's V)": 'N/A', 'Significance': 'N/A'})


    stat_results_df = pd.DataFrame(stat_results)
    report_parts.append("### Statistical Test Summary\n")
    report_parts.append(stat_results_df.to_markdown(index=False) + "\n")
    
    return report_parts, stat_results_df

def generate_markdown_report(
    report_sections: List[List[str]], 
    overall_stats_df: pd.DataFrame, 
    cost_eff_parts: List[str], # Specifically for parsing cost per task
    stat_results_df: pd.DataFrame
) -> None:
    """Generates the final Markdown report."""
    
    report_content: List[str] = ["# Benchmark Analysis Report: PDD vs. Claude\n"]
    report_content.append("This report analyzes and compares the performance of PDD and Claude AI coding assistants based on benchmark data.\n")

    # Executive Summary
    report_content.append("## Executive Summary\n")
    
    best_tool_overall = overall_stats_df.loc[overall_stats_df['overall_score'].idxmax()]['tool']
    pdd_overall_series = overall_stats_df[overall_stats_df['tool'] == 'PDD']
    claude_overall_series = overall_stats_df[overall_stats_df['tool'] == 'Claude']

    summary_points: List[str] = [
        f"- **Overall Winner (Weighted Score):** {best_tool_overall}"
    ]
    if not pdd_overall_series.empty:
        pdd_overall = pdd_overall_series.iloc[0]
        summary_points.append(f"- **PDD Performance:** Avg Time: {pdd_overall['avg_execution_time']:.2f}s, Avg Cost: ${pdd_overall['avg_api_cost']:.4f}, Success Rate: {pdd_overall['success_rate']:.2%}")
    if not claude_overall_series.empty:
        claude_overall = claude_overall_series.iloc[0]
        summary_points.append(f"- **Claude Performance:** Avg Time: {claude_overall['avg_execution_time']:.2f}s, Avg Cost: ${claude_overall['avg_api_cost']:.4f}, Success Rate: {claude_overall['success_rate']:.2%}")
    
    # Add cost-efficiency summary by parsing the markdown part from cost_eff_parts
    markdown_table_str = cost_eff_parts[1] # cost_eff_parts[0] is header, cost_eff_parts[1] is table
    lines = markdown_table_str.strip().split('\n')
    
    pdd_cost_val_str: Optional[str] = None
    claude_cost_val_str: Optional[str] = None

    # Expecting table rows like: | ToolName | TotalCost | NumSuccess | CostPerSuccess |
    # Indices after split('|'): 0="", 1="ToolName", 2="TotalCost", ..., 4="CostPerSuccess"
    for line_idx in range(2, len(lines)): # Start from index 2 (skip header and separator)
        cols = lines[line_idx].split('|')
        if len(cols) > 4: # Ensure enough columns for CostPerSuccess
            tool_name_in_col = cols[1].strip()
            cost_value = cols[4].strip()
            if "PDD" in tool_name_in_col:
                pdd_cost_val_str = cost_value
            elif "Claude" in tool_name_in_col:
                claude_cost_val_str = cost_value
    
    if pdd_cost_val_str and claude_cost_val_str:
        try:
            pdd_float = float(pdd_cost_val_str)
            claude_float = float(claude_cost_val_str)
            summary_points.append(f"- **Cost per Successful Task:** PDD: ${pdd_float:.4f}, Claude: ${claude_float:.4f}")
        except ValueError:
            summary_points.append("- Cost per Successful Task: Error parsing values from markdown table.")
    else:
        summary_points.append("- Cost per Successful Task: Data not found or table format unexpected in markdown.")

    # Add statistical significance summary
    for _, row in stat_results_df.iterrows():
        if row['Significance'] == 'Yes':
            effect_size_col_name = [col for col in row.index if "Effect Size" in col][0]
            effect_size_val = row[effect_size_col_name]
            metric_name = row['Metric']
            p_val = row['p-value']
            summary_points.append(f"- Statistically significant difference in **{metric_name}** (p={p_val}, {effect_size_col_name.split('(')[1][:-1]}={effect_size_val}).")
    
    report_content.append("\n".join(summary_points) + "\n")

    # Append all main sections
    for section_parts_list in report_sections:
        report_content.extend(section_parts_list)

    # Final Recommendation
    report_content.append("\n## 6. Final Recommendation\n")
    # Note: The recommendation part uses placeholders like "[mention specific areas...]"
    # These would ideally be filled dynamically if more detailed insights from dim_stats_parts etc. were parsed here.
    # For now, it's a template.
    recommendation = f"""
Based on this analysis:

- For tasks where **overall balanced performance (time, cost, success)** is critical, **{best_tool_overall}** is recommended due to its higher weighted score.
- If **minimizing API cost** is the absolute priority, analyze the 'Average API Cost' and 'Cost Per Successful Task' metrics. The tool with lower values here might be preferred, even if slightly slower or less successful.
- If **maximizing success rate** is paramount, the tool with the higher overall success rate and better performance on specific critical dimensions (e.g., specific languages or edit types) should be chosen.
- **PDD** shows strengths in [mention specific areas if evident, e.g., specific languages/file_sizes based on dimensional analysis].
- **Claude** shows strengths in [mention specific areas if evident, e.g., specific languages/file_sizes based on dimensional analysis].

Consider the specific context of your tasks (e.g., dominant language, typical file size, importance of speed vs. cost) when making a final decision.
Further investigation into common error patterns for each tool could lead to improved prompt engineering or identify areas where one tool might need more support.
"""
    report_content.append(recommendation)

    # Write report to file
    report_path = os.path.join(OUTPUT_DIR, 'benchmark_analysis.md')
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("\n".join(report_content))
    print(f"Markdown report saved to: {report_path}")


# --- Main Execution ---
def main() -> None:
    """Main function to run the benchmark analysis."""
    print("Starting benchmark analysis...")
    create_output_directory()
    
    df = load_and_prepare_data()
    if df is None:
        return

    report_sections_collector: List[List[str]] = []

    overall_parts, overall_stats_df = overall_performance_analysis(df)
    report_sections_collector.append(overall_parts)
    
    dim_stats_parts = dimension_specific_analysis(df)
    report_sections_collector.append(dim_stats_parts)
    
    # cost_efficiency_analysis no longer needs overall_stats_df
    cost_eff_parts = cost_efficiency_analysis(df)
    report_sections_collector.append(cost_eff_parts)
    
    success_err_parts, ci_df = success_and_error_analysis(df, overall_stats_df)
    report_sections_collector.append(success_err_parts)
    
    stat_sig_parts, stat_results_df = statistical_significance_analysis(df)
    report_sections_collector.append(stat_sig_parts)
    
    generate_markdown_report(
        report_sections=report_sections_collector, 
        overall_stats_df=overall_stats_df, 
        cost_eff_parts=cost_eff_parts, # Pass this specifically for parsing
        stat_results_df=stat_results_df
    )
    
    print("Benchmark analysis complete. Outputs are in the 'analysis/analysis_report/' directory.")

if __name__ == '__main__':
    main()
