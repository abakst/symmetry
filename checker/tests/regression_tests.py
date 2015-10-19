#!/usr/bin/env python

import argparse

parser = argparse.ArgumentParser(description='Regression testing script for Symmetry')

parser.add_argument('filename', nargs='*', help='files to test')

args = parser.parse_args()

HASKELL_COMMAND = ""
