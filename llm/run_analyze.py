import os
import pandas as pd
from custom_logger import logger
from analyzer import OptionInfoAnalyzer

USE_DEEPSEEK = True

BENCHMARK_INFO_PATH = "TODO:"
OUTPUT_DIR = "TODO:"
if not os.path.exists(BENCHMARK_INFO_PATH):
    raise FileNotFoundError(f"Benchmark info file does not exist: {BENCHMARK_INFO_PATH}")
if not os.path.exists(OUTPUT_DIR):
    raise FileNotFoundError(f"Output directory does not exist: {OUTPUT_DIR}")

def run_analyze():
    df = pd.read_csv(BENCHMARK_INFO_PATH)
    prog_names = df["program_name"].tolist()
    repo_paths = df["repo_path"].tolist()
    bc_paths = df["bc_path"].tolist()
    if len(prog_names) != len(repo_paths):
        raise ValueError("Mismatch in lengths of program names and repository paths.")
    ignore_programs = ["TODO:"]
    interested_programs = ["TODO:"]
    for prog_name, repo_path, bc_path in zip(prog_names, repo_paths, bc_paths):
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
        default_values_path = os.path.join(prog_output_dir, "default_values.txt")
        if not os.path.exists(default_values_path):
            raise FileNotFoundError(f"Default values path does not exist: {default_values_path}")
        check_constraints_path = os.path.join(prog_output_dir, "TODO:")
        check_global_constraints_path = os.path.join(prog_output_dir, "TODO:")

        save_path = os.path.join(prog_output_dir, "TODO:")
        if os.path.exists(save_path):
            logger.warning(f"Output file {save_path} already exists, skipping running analyze on program {prog_name}")
            continue

        analyzer = OptionInfoAnalyzer(repo_name=prog_name, prog_name=prog_name, option_info_filename="TODO:", output_dir=prog_output_dir, default_values_path=default_values_path, log_path=log_path, check_constraints_path=check_constraints_path, check_global_constraints_path=check_global_constraints_path)
        analyzer.analyze()
        analyzer.process_check_constraints()
        analyzer.process_check_global_constraints()

if __name__ == "__main__":
    run_analyze()