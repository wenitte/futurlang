import subprocess
import json
import logging

class FuturLangEnv:
    """
    A persistent interactive reinforcement learning environment wrapping the FuturLang kernel.
    """
    def __init__(self, node_bin='node', script_path='dist/cli.js'):
        self.node_bin = node_bin
        self.script_path = script_path
        self.process = None
        self._start_kernel()

    def _start_kernel(self):
        """Starts the persistent node repl."""
        cmd = [self.node_bin, self.script_path, 'repl', '--json']
        self.process = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1  # Line buffered
        )

    def close(self):
        """Terminates the interactive session."""
        if self.process:
            self.process.terminate()
            self.process = None

    def reset(self):
        """
        Resets the environment. Since the current fl repl holds state globally,
        we kill and restart the process to clear the partial proof map.
        """
        self.close()
        self._start_kernel()

    def step(self, action_string: str):
        """
        Submits a proof claim or assumption to the kernel.
        Returns (observation, reward, done, info).
        """
        if not self.process or self.process.poll() is not None:
            raise RuntimeError("Kernel process is fundamentally dead. Please check node installation.")

        # Write the action sequence to the stdin of the node process
        self.process.stdin.write(action_string + '\n')
        self.process.stdin.flush()

        # Block and read the resulting JSON trace
        try:
            line = self.process.stdout.readline()
            if not line:
                return {"error": "EOF"}, -1.0, True, {"raw": ""}
            
            response = json.loads(line)
        except json.JSONDecodeError:
            return {"error": "Invalid JSON from kernel"}, -1.0, True, {"raw": line}

        # Calculate RL reward based on the state of the trace
        reward = 0.0
        done = False
        info = response

        if response.get("status") == "ok" and "trace" in response:
            state = response["trace"].get("state")
            if state == "PROVED":
                reward = 1.0
                # A verified step is great. If it was the final target, the agent handles 'done'.
            elif state == "PENDING":
                reward = 0.1 # Small positive reward for a structurally valid but unresolved node
            elif state == "FAILED":
                reward = -1.0 # Invalid derivation attempt
                done = True # Commonly terminates the path attempt in search
        else:
            reward = -1.0
            done = True
            
        return response, reward, done, info

import queue

class FuturLangEnvPool:
    """
    Thread-safe resource pool for managing isolated FuturLang background evaluators.
    """
    def __init__(self, size=4, node_bin='node', script_path='dist/cli.js'):
        self.pool = queue.Queue(maxsize=size)
        self.size = size
        for _ in range(size):
            self.pool.put(FuturLangEnv(node_bin=node_bin, script_path=script_path))

    def get(self):
        return self.pool.get()

    def put(self, env):
        self.pool.put(env)

    def close(self):
        while not self.pool.empty():
            env = self.pool.get()
            env.close()
