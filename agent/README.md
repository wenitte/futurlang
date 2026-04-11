# FuturLang Python MCTS Scaffold

This directory provides the infrastructure required to loop an external Large Language Model (LLM) or reinforcement learning agent over the FuturLang kernel using Monte Carlo Tree Search (MCTS).

Since FuturLang is built strictly as a graph of sequential propositions verified by a categorical checker, an AI agent can step through a proof interactively, getting dense logical gradients (via FAILED tracebacks) if it predicts a structurally invalid term.

## Architecture

* `environment.py`: A standard stateful wrapper (`FuturLangEnv`). It launches `fl repl --json` as a persistent subprocess and communicates over `stdin/stdout`. It returns structured JSON causal bounds.
* `mcts.py`: Contains a basic text-based MCTS graph implementation that iteratively polls a policy function and backpropagates rewards.
* `test.py`: A mock integration showing how the pieces lock together.

## How to use

Ensure your FuturLang typescript root has been compiled first (`npm run build`).

Then run:
```bash
python3 agent/test.py
```
This will launch a Monte Carlo Tree Search attempting to logically verify the `SubsetTransport` formalization.

### Connecting a live LLM
To bridge this with OpenAI or another model, simply redefine `mock_llm_policy` in `test.py` to prompt the API. We recommend concatenating the `current_sequence` array and injecting the textual `message` and `causalError` payloads directly into the system prompt as negative feedback guidance.
