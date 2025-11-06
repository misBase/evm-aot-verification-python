"""Pytest configuration and shared fixtures for tests."""

import sys
import os

# Add project root to Python path for imports
project_root = os.path.join(os.path.dirname(__file__), '..')
if project_root not in sys.path:
    sys.path.insert(0, project_root)

