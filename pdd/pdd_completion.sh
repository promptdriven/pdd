#!/usr/bin/env bash

# PDD CLI Bash Completion Script
# Version: 0.0.5
# Supports all PDD commands and options with filename completion

_pdd() {
    local cur prev words cword
    
    # Replace _init_completion with manual initialization
    COMPREPLY=()
    cur="${COMP_WORDS[COMP_CWORD]}"
    prev="${COMP_WORDS[COMP_CWORD-1]}"
    words=("${COMP_WORDS[@]}")
    cword=$COMP_CWORD

    # Global options
    local global_opts="--force --strength --time --temperature --verbose --quiet --output-cost --review-examples --local --context --list-contexts --help --version"

    # Commands
    local commands="generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps verify sync setup install_completion pytest-output"

    # Command-specific options
    local generate_opts="--output --original-prompt --incremental --env -e"
    local example_opts="--output"
    local test_opts="--output --language --coverage-report --existing-tests --target-coverage --merge"
    local preprocess_opts="--output --xml --recursive --double --exclude"
    local fix_opts="--output-test --output-code --output-results --loop --verification-program --max-attempts --budget --auto-submit"
    local split_opts="--output-sub --output-modified"
    local change_opts="--output --csv --budget"
    local update_opts="--output --git"
    local detect_opts="--output"
    local conflicts_opts="--output"
    local crash_opts="--output --output-program --loop --max-attempts --budget"
    local trace_opts="--output"
    local bug_opts="--output --language"
    local auto_deps_opts="--output --csv --force-scan"
    local verify_opts="--output-results --output-code --output-program --max-attempts --budget"
    local sync_opts="--max-attempts --budget --skip-verify --skip-tests --target-coverage --log"
    local pytest_output_opts="--json-only"

    # Complete global options before command
    if [[ $cword -eq 1 ]]; then
        COMPREPLY=($(compgen -W "$global_opts $commands" -- "$cur"))
        return
    fi

    # Complete command-specific options
    case ${words[1]} in
        generate)
            # If completing the value for -e/--env, suggest environment variable names (with and without '=')
            if [[ $prev == "-e" || $prev == "--env" ]]; then
                local vars
                vars=$(env | cut -d= -f1 | sort -u)
                # Offer both KEY and KEY=
                local vars_with_eq
                vars_with_eq=$(printf '%s=\n' $vars)
                COMPREPLY=($(compgen -W "$vars $vars_with_eq" -- "$cur"))
                return
            fi
            _complete_files ".prompt"
            COMPREPLY+=($(compgen -W "$generate_opts" -- "$cur"))
            ;;
        example)
            _complete_files ".prompt"
            _complete_files
            COMPREPLY+=($(compgen -W "$example_opts" -- "$cur"))
            ;;
        test)
            _complete_files ".prompt"
            _complete_files
            COMPREPLY+=($(compgen -W "$test_opts" -- "$cur"))
            ;;
        preprocess)
            _complete_files ".prompt"
            COMPREPLY+=($(compgen -W "$preprocess_opts" -- "$cur"))
            ;;
        fix)
            _complete_files ".prompt"
            _complete_files
            _complete_files
            _complete_files
            COMPREPLY+=($(compgen -W "$fix_opts" -- "$cur"))
            ;;
        split)
            _complete_files ".prompt"
            _complete_files
            _complete_files
            COMPREPLY+=($(compgen -W "$split_opts" -- "$cur"))
            ;;
        change)
            _complete_files ".prompt"
            _complete_files
            if [[ $prev != "--csv" && ${COMP_WORDS[COMP_CWORD-2]} != "--csv" ]]; then
                 _complete_files ".prompt"
            fi
            COMPREPLY+=($(compgen -W "$change_opts" -- "$cur"))
            ;;
        update)
            _complete_files ".prompt"
            _complete_files
            if [[ ! " ${words[@]} " =~ " --git " ]]; then
                _complete_files
            fi
            COMPREPLY+=($(compgen -W "$update_opts" -- "$cur"))
            ;;
        detect)
            _complete_files ".prompt"
            COMPREPLY+=($(compgen -W "$detect_opts" -- "$cur"))
            ;;
        conflicts)
            _complete_files ".prompt"
            _complete_files ".prompt"
            COMPREPLY+=($(compgen -W "$conflicts_opts" -- "$cur"))
            ;;
        crash)
            _complete_files ".prompt"
            _complete_files
            _complete_files
            _complete_files
            COMPREPLY+=($(compgen -W "$crash_opts" -- "$cur"))
            ;;
        trace)
            _complete_files ".prompt"
            _complete_files
            COMPREPLY+=($(compgen -W "$trace_opts" -- "$cur"))
            ;;
        bug)
            _complete_files ".prompt"
            _complete_files
            _complete_files
            _complete_files
            _complete_files
            COMPREPLY+=($(compgen -W "$bug_opts" -- "$cur"))
            ;;
        auto-deps)
            _complete_files ".prompt"
            COMPREPLY+=($(compgen -W "$auto_deps_opts" -- "$cur"))
            ;;
        verify)
            _complete_files ".prompt"
            _complete_files
            _complete_files
            COMPREPLY+=($(compgen -W "$verify_opts" -- "$cur"))
            ;;
        sync)
            # BASENAME (not a file), offer options
            COMPREPLY+=($(compgen -W "$sync_opts" -- "$cur"))
            ;;
        setup)
            # no command-specific options
            ;;
        install_completion)
            # no command-specific options
            ;;
        pytest-output)
            _complete_files
            COMPREPLY+=($(compgen -W "$pytest_output_opts" -- "$cur"))
            ;;
        *)
            COMPREPLY=($(compgen -W "$global_opts" -- "$cur"))
            ;;
    esac
}

_complete_files() {
    local ext=$1
    local files
    if [[ "$cur" == -* ]]; then
        return
    fi

    if [[ -n $ext ]]; then
        files=$(compgen -f -X "!*${ext}" -- "$cur")
        COMPREPLY+=($(compgen -f -o plusdirs -X "!*${ext}" -- "$cur" | awk -v e="$ext" '$0 ~ e"$"{ COMPREPLY+=($0) }'))
        files=$(echo "${files}" | awk '!seen[$0]++')

    else
        files=$(compgen -f -o plusdirs -- "$cur")
    fi
    if [[ -n "$files" ]]; then
       COMPREPLY+=($(compgen -W "$files" -- "$cur"))
    fi
}

complete -F _pdd pdd
