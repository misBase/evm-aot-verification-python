"""测试的Pytest配置和共享夹具。"""

import sys
import os

# 将项目根目录添加到Python路径以便导入
project_root = os.path.join(os.path.dirname(__file__), '..')
if project_root not in sys.path:
    sys.path.insert(0, project_root)
