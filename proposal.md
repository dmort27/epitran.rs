# Epitran2, a Fast, Safe, Flexible Multilingual Grapheme-to-Phoneme Transducer Implemented in Rust

## Motivation

Epitran is likely the most widely used multilingual grapheme-to-phoneme, or G2P, system. A G2P system converts text in standard spelling to pronunciations represented using a phonetic transcription system like the International Phonetic Alphabet. Epitran supports over 100 languages, but is slow (it is written in Python), is architecturally fragmented, and uses supoptimal algorithms in some cases (for example, it uses an WFST-based paired-ngram model for English). Epitran would be dramatically more useful if it were faster, more reliable, and easier to extend. Rewriting the project in Rust (and providing a python wrapper) would allow a team to accomplish all of these goals.

## What has been done

For languages with transparent orthographies (spelling systems) support is rule-based. Code that compiles these rules into WFSTs has been written. A basic sketch of the overall architecture exists.

## What has to be done

### Research

- Determine best supervised algorithms for G2P for highly ambiguous orthographies like English, Arabic, and Urdu need to developed. Ideally, such algorithms will be executable efficiently on a CPU (though ability to exploit GPU resources would also be beneficial).
- Explore distant supervision from speech as a means of improving G2P models. Some research exists in this area, but we can do better.

### Development

- The dictionary-based component of the system must be written.
- The supervised models must be adapted to the Rust ecosystem (perhaps using tch-rs).
- The rule-based component of the system must be completed.
- The user-facing API must be implemented.
- The project should be set up with comprehensive tests and continuous integration
