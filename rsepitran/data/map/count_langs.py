#!/usr/bin/env python

import glob
import re

langs = set()

for fn in glob.glob('*.csv'):
    if lang := re.match('([a-z]{3})[-]', fn):
        langs.add(lang.group(1))

print(len(langs))