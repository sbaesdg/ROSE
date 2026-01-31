import os
import pandas as pd
from repo_analyzer import RepoAnalyzer
from repo_extractor import RepoExtractor
from custom_logger import logger

ALL_STAGES = ["process_repo", "analyze", "find_symbolization_line", "resolve_macro", "add_check_constraints"]
RUN_STAGES = ALL_STAGES[:5]
for i, stage in enumerate(RUN_STAGES):
    if stage != ALL_STAGES[i]:
        raise ValueError(f"RUN_STAGES {RUN_STAGES} is not a prefix of ALL_STAGES {ALL_STAGES}")

BENCHMARK_INFO_PATH = "TODO:"
OUTPUT_DIR = "TODO:"
if not os.path.exists(BENCHMARK_INFO_PATH):
    raise FileNotFoundError(f"Benchmark info file does not exist: {BENCHMARK_INFO_PATH}")
if not os.path.exists(OUTPUT_DIR):
    raise FileNotFoundError(f"Output directory does not exist: {OUTPUT_DIR}")

def run_extract():
    df = pd.read_csv(BENCHMARK_INFO_PATH)
    prog_names = df["program_name"].tolist()
    repo_paths = df["repo_path"].tolist()
    bc_paths = df["bc_path"].tolist()
    program_manual_paths = df["program_manual_path"].tolist()
    if len(prog_names) != len(repo_paths):
        raise ValueError("Mismatch in lengths of program names and repository paths.")
    all_programs = ["TODO:"]
    ignore_programs = ["TODO:"]
    interested_programs = ["TODO:"]
    for prog_name, repo_path, bc_path, program_manual_path in zip(prog_names, repo_paths, bc_paths, program_manual_paths):
        if prog_name in ignore_programs:
            continue
        if interested_programs and prog_name not in interested_programs:
            continue
        assert os.path.exists(bc_path), f"BC path not found for program: {prog_name}"
        logger.info(f"Processing program: {prog_name}, repository path: {repo_path}, BC path: {bc_path}")
        prog_output_dir = os.path.join(OUTPUT_DIR, prog_name)
        if not os.path.exists(prog_output_dir):
            os.makedirs(prog_output_dir)
        log_path = os.path.join(prog_output_dir, "log.log")
        if not os.path.exists(repo_path):
            raise FileNotFoundError(f"Repository path does not exist: {repo_path}")
        print(f"Processing {prog_name} at {repo_path}")
        analyzer = RepoAnalyzer(
            repo_path=repo_path,
            prog_name=prog_name,
            output_dir=prog_output_dir,
            log_path=log_path,
            bc_path=bc_path,
            program_manual_path=program_manual_path
        )
        if 'process_repo' in RUN_STAGES:
            analyzer.process_repo()
        if 'analyze' in RUN_STAGES:
            thread_cnt = 10
            group_cnt = 5
            analyzer.parse_and_analyze_in_parallel(thread_cnt=thread_cnt, group_cnt=group_cnt)
        if 'find_symbolization_line' in RUN_STAGES:
            analyzer.find_symbolization_line()
        if 'resolve_macro' in RUN_STAGES:
            thread_cnt = 10
            group_cnt = 5
            analyzer.resolve_macro_in_parallel(thread_cnt=thread_cnt, group_cnt=group_cnt)
        if 'add_check_constraints' in RUN_STAGES:
            analyzer.segment_code()
            thread_cnt = 10
            group_cnt = 5
            analyzer.add_check_constraints_in_parallel(thread_cnt=thread_cnt, group_cnt=group_cnt)
            analyzer.add_global_check_constraints()
        print(f"Finished processing program: {prog_name}")

if __name__ == "__main__":
    run_extract()