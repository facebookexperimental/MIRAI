# Contributing to Mirai
We welcome contributions and want to make contributing to this project as easy and transparent as
possible. A background in compilers and static analysis will be very useful for contributing to the main
code base, but there are ample opportunities for other contributions as well. Test cases and motivating examples
are particularly welcome.

## Our Development Process
Every pull request should have a description that motivates it and
should have tests that cover all of the source lines touched and added by the request. No pull request will be merged
unless all tests are passing.

A TODO comment should include the number of an issue that describes the outstanding work in greater detail.

All APIs should be [documented](https://rust-lang-nursery.github.io/api-guidelines/documentation.html) in the code and
all public methods and functions should have explicit assertion statements to document and enforce any preconditions 
that they depend on.

A pull request that is a work in progress that has been published to get help and feedback from the community should
be tagged with WIP.

The person approving a pull request will also merge it into master.

## Pull Requests
We actively welcome your pull requests.

1. Fork the repo and create your branch from `master`.
2. If you've added code that should be tested, add tests.
3. If you've changed APIs, update the documentation.
4. Ensure the test suite passes.
5. Make sure your code lints.
6. If you haven't already, complete the Contributor License Agreement ("CLA").

## Contributor License Agreement ("CLA")
In order to accept your pull request, we need you to submit a CLA. You only need
to do this once to work on any of Facebook's open source projects.

Complete your CLA here: <https://code.facebook.com/cla>

## Issues
We use GitHub issues to track public bugs. Please ensure your description is
clear and has sufficient instructions to be able to reproduce the issue.

Facebook has a [bounty program](https://www.facebook.com/whitehat/) for the safe
disclosure of security bugs. In those cases, please go through the process
outlined on that page and do not file a public issue.

## Coding Style
We use the [Rust style guide](https://github.com/rust-lang-nursery/fmt-rfcs/blob/master/guide/guide.md)

## License
By contributing to Mirai, you agree that your contributions will be licensed
under the LICENSE file in the root directory of this source tree.