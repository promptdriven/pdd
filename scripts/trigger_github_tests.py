#!/usr/bin/env python3
"""
Script to trigger GitHub Actions test workflow from local machine.

Usage:
    python scripts/trigger_github_tests.py
    python scripts/trigger_github_tests.py --branch feat/your-branch
    python scripts/trigger_github_tests.py --pr-number 123
    python scripts/trigger_github_tests.py --pr-number 123 --pr-url https://github.com/promptdriven/pdd_cloud/pull/123
    python scripts/trigger_github_tests.py --branch feat/your-branch --pr-number 456
"""

import argparse
import os
import requests
import sys
from typing import Optional


class GitHubWorkflowTrigger:
    def __init__(self):
        self.github_token = os.getenv('GITHUB_TOKEN')
        self.repo = 'gltanaka/pdd'
        self.workflow_file = 'pr-tests.yml'
        
        if not self.github_token:
            print("❌ Error: GITHUB_TOKEN environment variable not set")
            print("   Set it with: export GITHUB_TOKEN='your_personal_access_token'")
            print("   Or create a .env file with: GITHUB_TOKEN=your_token")
            sys.exit(1)
    
    def trigger_workflow(self, branch: str = 'main', pr_number: Optional[str] = None, pr_url: Optional[str] = None) -> bool:
        """Trigger the GitHub Actions workflow."""
        url = f'https://api.github.com/repos/{self.repo}/actions/workflows/{self.workflow_file}/dispatches'
        
        headers = {
            'Accept': 'application/vnd.github+json',
            'Authorization': f'Bearer {self.github_token}',
            'X-GitHub-Api-Version': '2022-11-28'
        }
        
        data = {'ref': branch}
        
        if pr_number or pr_url:
            data['inputs'] = {}
            if pr_number:
                data['inputs']['pr_number'] = str(pr_number)
            if pr_url:
                data['inputs']['pr_url'] = pr_url
        
        try:
            print(f"🚀 Triggering GitHub Actions workflow...")
            print(f"   Repository: {self.repo}")
            print(f"   Branch: {branch}")
            if pr_number:
                print(f"   PR Number: {pr_number}")
            if pr_url:
                print(f"   PR URL: {pr_url}")
            
            response = requests.post(url, headers=headers, json=data)
            
            if response.status_code == 204:
                print(f"✅ Workflow triggered successfully!")
                print(f"   View progress: https://github.com/{self.repo}/actions")
                return True
            else:
                print(f"❌ Failed to trigger workflow: {response.status_code}")
                print(f"   Response: {response.text}")
                return False
                
        except requests.exceptions.RequestException as e:
            print(f"❌ Network error: {e}")
            return False
    
    def check_workflow_status(self) -> None:
        """Check the status of recent workflow runs."""
        url = f'https://api.github.com/repos/{self.repo}/actions/workflows/{self.workflow_file}/runs'
        
        headers = {
            'Accept': 'application/vnd.github+json',
            'Authorization': f'Bearer {self.github_token}',
            'X-GitHub-Api-Version': '2022-11-28'
        }
        
        try:
            response = requests.get(url, headers=headers, params={'per_page': 5})
            
            if response.status_code == 200:
                runs = response.json().get('workflow_runs', [])
                print(f"\n📊 Recent workflow runs:")
                for run in runs[:3]:  # Show last 3 runs
                    status = run['status']
                    conclusion = run['conclusion']
                    created_at = run['created_at'][:19].replace('T', ' ')
                    
                    if conclusion == 'success':
                        status_icon = "✅"
                    elif conclusion == 'failure':
                        status_icon = "❌"
                    elif conclusion == 'cancelled':
                        status_icon = "⏹️"
                    else:
                        status_icon = "🔄"
                    
                    print(f"   {status_icon} {created_at} - {status} ({conclusion})")
                    print(f"      Branch: {run['head_branch']}")
                    print(f"      URL: {run['html_url']}")
                    print()
            else:
                print(f"❌ Failed to get workflow status: {response.status_code}")
                
        except requests.exceptions.RequestException as e:
            print(f"❌ Network error checking status: {e}")


def main():
    parser = argparse.ArgumentParser(description='Trigger GitHub Actions test workflow')
    parser.add_argument('--branch', default='main', help='Branch to test (default: main)')
    parser.add_argument('--pr-number', help='PR number to test')
    parser.add_argument('--pr-url', help='PR URL to test')
    parser.add_argument('--status', action='store_true', help='Check recent workflow status')
    
    args = parser.parse_args()
    
    trigger = GitHubWorkflowTrigger()
    
    if args.status:
        trigger.check_workflow_status()
        return
    
    # Validate inputs
    if args.pr_url and not args.pr_number:
        print("❌ Error: --pr-url requires --pr-number")
        sys.exit(1)
    
    # Trigger the workflow
    success = trigger.trigger_workflow(
        branch=args.branch,
        pr_number=args.pr_number,
        pr_url=args.pr_url
    )
    
    if success:
        print(f"\n💡 Tips:")
        print(f"   - Check progress: https://github.com/{trigger.repo}/actions")
        print(f"   - View logs: Click on the running workflow")
        print(f"   - Check status: python scripts/trigger_github_tests.py --status")
        
        if args.pr_number:
            print(f"   - PR will be commented with results when tests complete")
    
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
