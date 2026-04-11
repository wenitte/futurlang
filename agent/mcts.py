import math
import random
from typing import List, Tuple
from environment import FuturLangEnv

class MCTSNode:
    def __init__(self, state_sequence: List[str], parent=None):
        self.state_sequence = state_sequence
        self.parent = parent
        self.children = []
        self.visits = 0
        self.value = 0.0
        self.is_terminal = False

    def ucb1(self, c=1.41):
        if self.visits == 0:
            return float('inf')
        return (self.value / self.visits) + c * math.sqrt(math.log(self.parent.visits) / self.visits)

class MathSearch:
    def __init__(self, env: FuturLangEnv, policy_fn):
        self.env = env
        self.policy_fn = policy_fn

    def search(self, root_state: List[str], iterations=10):
        root = MCTSNode(root_state)

        for _ in range(iterations):
            # Select
            node = self._select(root)

            # Expand
            if not node.is_terminal:
                self._expand(node)
                if node.children:
                    node = random.choice(node.children)

            # Simulate
            reward = self._simulate(node)

            # Backpropagate
            self._backpropagate(node, reward)

        if not root.children:
            return None
        
        # Return the best sequence
        best_child = max(root.children, key=lambda c: c.visits)
        return best_child.state_sequence

    def _select(self, node: MCTSNode) -> MCTSNode:
        while node.children and not node.is_terminal:
            unvisited = [c for c in node.children if c.visits == 0]
            if unvisited:
                return random.choice(unvisited)
            node = max(node.children, key=lambda c: c.ucb1())
        return node

    def _expand(self, node: MCTSNode):
        # Poll the policy model (e.g. LLM) to get candidate next steps
        candidates = self.policy_fn(node.state_sequence)
        for action in candidates:
            # We treat the sequence of text steps as the state trail
            child = MCTSNode(node.state_sequence + [action], parent=node)
            node.children.append(child)

    def _simulate(self, node: MCTSNode) -> float:
        # Re-roll environment to clean state
        self.env.reset()
        
        total_reward = 0.0
        for action in node.state_sequence:
            obs, reward, done, info = self.env.step(action)
            total_reward += reward
            if done:
                node.is_terminal = True
                break
                
        return total_reward

    def _backpropagate(self, node: MCTSNode, reward: float):
        while node is not None:
            node.visits += 1
            node.value += reward
            node = node.parent
