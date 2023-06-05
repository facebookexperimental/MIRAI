# Tag Analysis on Substrate Pallets

>The work documented here is funded by the [Web3 Foundation](https://github.com/w3f/Grants-Program/tree/master), our proposal can be found [here](https://github.com/w3f/Grants-Program/blob/master/applications/sarp-basic-functionality.md).

## Introduction

[Runtime Pallets](https://docs.substrate.io/learn/runtime-development/) are modules for writing the business logic of blockchains in [Substrate](https://github.com/paritytech/substrate) (a Rust framework for building blockchains). These are usually concise pieces of standalone code with relatively few dependencies and clear specifications, hence tractable targets for performing static analysis and verification. The code quality of a runtime pallet is crucial, as even minor defects can result in major exploits like DoS attacks or the stealing of funds by a malicious party. A static code analysis can help to automate the auditing processes and prevent introduction of defects throughout the software life-cycle.

We plan to develop a tool - SARP (Static Analysis tool for Runtime Pallets) to perform static analysis with reasonable soundness guarantees. In particular, we would like to target vunerability classes that are detectable using dataflow analysis techniques like *tag analysis* and *taint analysis*.

## Research
As a first step we analyzed the feasibility for using MIRAI to implement a static code analysis on substrate pallets. We investigated how the following vulnerability classes can be addressed with a tag analysis:

* [incorrect origin](https://github.com/bhargavbh/MIRAI/blob/main/substrate_examples/incorrect-origin/description.md) of dispatchable functions.
* [unsigned transaction](https://github.com/bhargavbh/MIRAI/blob/main/substrate_examples/unsigned-transaction/description.md) validation.

### Implementation
For each vulnerability class, we implemented prototype code to show, how the vulnerability can be detected:
* [Incorrect Origin](pallet_template/README.md)
* [TODO: Unsigned Transactions](offchain-worker/README.md)

### Findings
The research showed two main problems, when implementing a tag-analysis with MIRAI on substrate pallets:
1. **Complexity due to substrate macros** Ideally SARP only analyzes the newly written code of a pallet. To write a pallet one has to add several macros, which add a lot of complexity to the code in the background. Running a MIRAI analysis on a pallet, includes an analyzis on the macro code. This results in timeouts and reduces the certainty on issues found.
2. **Invasiveness of tag analysis** The code we wrote in our PoC is very invasive and changes the code of the pallet. This is not practical for end-users. Ideally the user doesn't need to change anything on their code, or at least the changes should be very simple.

### Next Steps
Before starting an implementation, a detailed software design should be worked out, addressing the issues from our findings.