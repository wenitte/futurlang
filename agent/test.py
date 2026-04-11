from environment import FuturLangEnv
from mcts import MathSearch
import subprocess

def mock_llm_policy(current_sequence):
    """
    Simulates a language model picking the next most likely logical operators.
    In a real implementation, you would feed the current_sequence and the causal error trace
    into a transformer model via an API call.
    """
    depth = len(current_sequence)
    if depth == 0:
        return ["assume(A ⊆ B)", "assert(A ⊆ B)"]  # The LLM guesses correctly and incorrectly
    elif depth == 1:
        if current_sequence[0] == "assume(A ⊆ B)":
            return ["assume(x ∈ A)", "assume(B ⊆ C)"]
    elif depth == 2:
        if current_sequence[0] == "assume(A ⊆ B)" and current_sequence[1] == "assume(x ∈ A)":
            return ["assert(x ∈ B)", "assert(x ∈ C)"]
            
    return []

def run_subset_transport_demonstration():
    print("Initializing FuturLang RL Agent Test...")
    
    # You might need to change node to the full path of the node binary if not in PATH natively.
    # We attempt to find the right node binary automatically if possible.
    try:
        node_bin = subprocess.check_output(['bash', '-c', 'which node || find ~/.nvm -name node -type f -executable 2>/dev/null | head -n 1']).decode('utf-8').strip()
    except Exception:
        node_bin = 'node'
        
    if not node_bin:
        node_bin = 'node'
        
    env = FuturLangEnv(node_bin=node_bin)
    searcher = MathSearch(env, mock_llm_policy)
    
    print("Starting Monte Carlo Tree Search...")
    best_path = searcher.search([], iterations=15)
    
    print("\nBest discovered proof path found by MCTS:")
    if best_path:
        for idx, step in enumerate(best_path):
            print(f"Step {idx+1}: {step}")
            
        print("\nVerifying winning path...")
        env.reset()
        for action in best_path:
            obs, rew, done, info = env.step(action)
            print(f"[{action}] -> Reward: {rew}")
            if "error" in obs:
               print("Error:", obs["error"])
    else:
        print("Failed to find a valid proof path.")
        
    env.close()

if __name__ == "__main__":
    run_subset_transport_demonstration()
