import os
import subprocess

def run_cfmtoolbox(directory, output_file):
    """
    Execute the specified command for every JSON file in the given directory and store the output in a file.

    Args:
        directory (str): Path to the directory containing JSON files.
        output_file (str): Path to the file where the output will be stored.
    """
    # Ensure the directory exists
    if not os.path.isdir(directory):
        print(f"Error: Directory '{directory}' does not exist.")
        return

    # Open the output file
    with open(output_file, "w") as output:
        # List all files in the directory
        files = os.listdir(directory)

        # Iterate over each file
        for file in files:
            # Check if the file has a .json extension
            if file.endswith(".json"):
                json_path = os.path.join(directory, file)

                # Construct the command
                command = [
                    "time", "python3", "-m", "cfmtoolbox",
                    "--import", json_path, analyse_command
                    
                ]

                # Print the command being executed
                print(f"Running command for: {file}")

                try:
                    # Execute the command and capture output
                    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,  # Capture standard output
                        stderr=subprocess.PIPE)    # Capture standard error (timing info))
                    # Write the output to the file
                    output.write(f"Output for {file}:\n")
                    output.write(result.stdout)
                    output.write(f"Time needed: {result.stderr}")
                    output.write("\n")
                except subprocess.CalledProcessError as e:
                    error_message = f"Command failed for {file}: {e}\n"
                    print(error_message)
                    output.write(error_message)

if __name__ == "__main__":
    # Replace 'your_directory_path' with the path to your directory containing JSON files
    # Replace 'output_file_path' with the desired output file path
    directory_path = "cfmtoolbox-smt-encoder/cfms/"
    output_file_path = "./output.txt"
    analyse_command = "run-csp-solver-maximize-cardinalities"

    run_cfmtoolbox(directory_path, output_file_path)
