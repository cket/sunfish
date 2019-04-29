#!/usr/bin/env pypy
# -*- coding: utf-8 -*-
import unittest
import sunfish

from unittest.mock import patch



class Tests(unittest.TestCase):

    @patch('sunfish.test_moves', return_value=['g2g4','f2f4','f4f5'])
    def test_fool(self, input):
        """
        This will run the engine and test fools mate to do a sanity test.
        """
        sunfish.main()


if __name__ == '__main__':
    unittest.main()
