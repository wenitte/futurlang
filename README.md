# FuturLang (.fl)

A formal proof language that combines mathematical rigor with programming language readability.

## Getting Started

### Installation

# Clone the repository
git clone https://github.com/wenitte/futurlang
cd futurlang

# Install dependencies
npm install

# Link globally
npm link


### Your First Proof
Create a file `hello.fl`:

theorem Hello_World() {
  assert(
    "Hello World can be proven"
  ) &&

  let message = "Hello World";
  assert(message == "Hello World");
}


## Language Features

### Theorems
- Case-insensitive names (no duplicates allowed)
- All statements must be logically connected
- Every theorem must evaluate to a truth value
- Can contain variable declarations

### Assertions
Two types:
- String assertions: `assert("message")`
- Variable equality: `assert(var == value)`

### Variables
Declare with let:

let variableName = value;


## Roadmap
- [ ] Logical connectives (⇒, ∧, ∨, ↔)
- [ ] Definition support
- [ ] Lemma support
- [ ] Proof methods
- [ ] Type system
