# Tag Analysis on Substrate Pallets

>The work documented here is funded by the [Web3 Foundation](https://github.com/w3f/Grants-Program/tree/master), our proposal can be found [here](https://github.com/w3f/Grants-Program/blob/master/applications/sarp-basic-functionality.md).

## Introduction

[Runtime Pallets](https://docs.substrate.io/learn/runtime-development/) are modules for writing the business logic of blockchains in [Substrate](https://github.com/paritytech/substrate) (a Rust framework for building blockchains). These are usually concise pieces of standalone code with relatively few dependencies and clear specifications, hence tractable targets for performing static analysis and verification. The code quality of a runtime pallet is crucial, as even minor defects can result in major exploits like DoS attacks or the stealing of funds by a malicious party. A static code analysis can help to automate the auditing processes and prevent introduction of defects throughout the software life-cycle.

We plan to develop a tool - SARP (Static Analysis tool for Runtime Pallets) to perform static code analysis on substrate pallets. In particular, we would like to target vunerability classes that are detectable using dataflow analysis techniques like *tag analysis* and *taint analysis*.

## Research
As a first step we analyzed the feasibility for using MIRAI to implement a static code analysis on substrate pallets. We investigated how the following vulnerability classes can be addressed with a tag analysis:

* [incorrect origin](https://github.com/bhargavbh/MIRAI/blob/main/substrate_examples/incorrect-origin/description.md) of dispatchable functions.
* [unsigned transaction](https://github.com/bhargavbh/MIRAI/blob/main/substrate_examples/unsigned-transaction/description.md) validation.

### Implementation
For each vulnerability class, we implemented prototype code to show, how the vulnerability can be detected:
* [Incorrect Origin](pallet_template/README.md)
* [Unsigned Transactions](offchain-worker/README.md)

### Findings
The research showed three main problems:
1. **Crashes and timeouts of MIRAI** Certain pieces of substrate code lead to crashes of MIRAI. In other cases, parts of the code are not analyzed/do not produce warnings, because MIRAI runs into a timeout before reaching this code. Because of this, our examples are rather simple and we couldn't add and check tags at the locations we originally wanted to.
2. **Complexity due to substrate macros** The main reason for crashes and timeouts in our examples, was caused by substrate macros, adding a lot of complexity to the code in the background. Ideally SARP only analyzes the newly written code of a pallet.
4. **Invasiveness of tag analysis** The code we wrote in our PoC is very invasive and changes the code of the pallet. This is not practical for end-users. Ideally the user doesn't need to change anything on their code, or at least the changes should be very simple.


### Feasibility of Approach
With this first research project we could not completely determine the feasibility of the approach. To our current knowledge, the following points must be analyzed first:
1. Running the analysis only on the newly written pallet code - without the substrate macros. This should significantly reduce the complexity of the analysis. It should be possible to achieve this, by working out a software design, that separates the two.
2. It is currently unclear if all failures we observed result from the complexity of the code or from bugs within MIRAI. This needs further analysis.