// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "./DABEInterface.sol";

contract DABEManager is DABEInterface {
    address public immutable systemAdmin;
    bytes private globalParameter; // 全局参数

    // 机构属性（机构id => 机构信息）
    mapping(string => Institution) private institutions;

    // 用户映射
    mapping(address => User) private users;
    mapping(address => mapping(string => Attribute[])) private userAttributes;

    // 数据记录 (数据id => 数据记录)
    mapping(string => DataRecord) private dataRecords;

    constructor(address _systemAdmin, bytes memory _globalParameter) {
        systemAdmin = _systemAdmin;
        globalParameter = _globalParameter;
    }

    modifier onlySystemAdmin() {
        require(msg.sender == systemAdmin, "Only system admin can perform this action");
        _;
    }

    modifier onlyAttributeAdmin(string memory institutionId) {
        require(msg.sender == institutions[institutionId].attributeAdmin, "Only attribute admin can perform this action");
        _;
    }

    function registerInstitution(string calldata institutionId, address attributeAdmin, string[] memory attributeIds, bytes calldata pk) external override {
        require(bytes(institutionId).length > 0, "Institution ID is required");
        require(attributeAdmin != address(0), "Attribute admin address is required");
        require(attributeIds.length > 0, "At least one attribute ID is required");
        require(pk.length > 0, "Public key is required");
        require(areAttributeIdsUnique(attributeIds), "Attribute IDs must be unique");
        require(institutions[institutionId].status == ApprovalStatus.NotRegistered, "Institution already registered");

        institutions[institutionId] = Institution(institutionId, msg.sender, ApprovalStatus.Pending, attributeAdmin, attributeIds, pk);
        emit InstitutionRegistered(institutionId, attributeIds);
    }

    function updateInstitutionInfo(string calldata institutionId, address attributeAdmin, string[] memory attributeIds, bytes calldata pk) external override {
        Institution storage institution = institutions[institutionId];
        require(institution.status != ApprovalStatus.NotRegistered, "Institution not registered");
        require(institution.status == ApprovalStatus.Pending, "Institution already approved/rejected");
        require(msg.sender == institution.creator, "Only institution creator can update");

        if (attributeAdmin != address(0)) {
            institution.attributeAdmin = attributeAdmin;
        }

        if (attributeIds.length > 0) {
            require(areAttributeIdsUnique(attributeIds), "Attribute IDs must be unique");
            institution.attributeIds = attributeIds;
        }

        if (pk.length > 0) {
            institution.pk = pk;
        }
    }

    function updateInstitutionStatus(string calldata institutionId, ApprovalStatus newStatus) external override onlySystemAdmin {
        Institution storage institution = institutions[institutionId];
        require(institution.status != ApprovalStatus.NotRegistered, "Institution not registered");
        require(institution.status == ApprovalStatus.Pending, "Institution already approved/rejected");
        require(newStatus != ApprovalStatus.NotRegistered && newStatus != ApprovalStatus.Pending, "Invalid status");

        institution.status = newStatus;
        emit InstitutionStatusChanged(institutionId, newStatus);
    }

    function getInstitutionInfo(string calldata institutionId) external view override returns (Institution memory) {
        return institutions[institutionId];
    }

    function registerUser(bytes calldata publicKey) external override {
        require(users[msg.sender].status == ApprovalStatus.NotRegistered, "User already registered");
        require(publicKey.length > 0, "Public key is required");

        users[msg.sender] = User(msg.sender, ApprovalStatus.Pending, publicKey);
        emit UserRegistered(msg.sender, publicKey);
    }

    function addUserAttribute(string calldata institutionId, string[] memory attributeIds) external override {
        require(institutions[institutionId].status == ApprovalStatus.Approved, "Institution not approved");
        require(users[msg.sender].status == ApprovalStatus.Approved, "User not approved");
        require(attributeIds.length > 0, "At least one attribute ID is required");
        require(areAttributeIdsValid(institutionId, attributeIds), "Invalid attribute IDs");

        Attribute[] storage attrs = userAttributes[msg.sender][institutionId];

        for (uint i = 0; i < attributeIds.length; i++) {
            for (uint j = 0; j < attrs.length; j++) {
                require(keccak256(bytes(attrs[j].id)) != keccak256(bytes(attributeIds[i])), "Attribute already exists");
            }
            attrs.push(Attribute(attributeIds[i], ApprovalStatus.Pending));
        }

        emit UserAttributeAdded(msg.sender, institutionId, attributeIds);
    }

    function updateUserAttributeStatus(address userAddress, string calldata institutionId, string[] memory attributeIds, ApprovalStatus newStatus) external override onlyAttributeAdmin(institutionId) {
        require(institutions[institutionId].status == ApprovalStatus.Approved, "Institution not approved");
        require(newStatus != ApprovalStatus.NotRegistered && newStatus != ApprovalStatus.Pending, "Invalid status");
        require(attributeIds.length > 0, "At least one attribute ID is required");

        Attribute[] storage attrs = userAttributes[userAddress][institutionId];
        for (uint i = 0; i < attributeIds.length; i++) {
            bool found = false;
            for (uint j = 0; j < attrs.length; j++) {
                if (keccak256(bytes(attrs[j].id)) == keccak256(bytes(attributeIds[i])) && attrs[j].status != newStatus) {
                    require(attrs[j].status == ApprovalStatus.Pending, "Attribute already approved/rejected");
                    attrs[j].status = newStatus;
                    found = true;
                    break;
                }
            }
            require(found, string(abi.encodePacked("Attribute not found: ", attributeIds[i])));
        }

        emit UserAttributeStatusChanged(userAddress, institutionId, attributeIds, newStatus);
    }

    function updateUserStatus(address userAddress, ApprovalStatus newStatus) external override onlySystemAdmin {
        User storage user = users[userAddress];
        require(user.status != ApprovalStatus.NotRegistered, "User not registered");
        require(user.status == ApprovalStatus.Pending, "User already approved/rejected");
        require(newStatus == ApprovalStatus.Approved || newStatus == ApprovalStatus.Rejected, "Invalid status");

        user.status = newStatus;
        emit UserStatusChanged(userAddress, newStatus);
    }

    function getUserPublicKey(address userAddress) external view override returns (bytes memory) {
        return users[userAddress].publicKey;
    }

    function getUserAttributes(address userAddress, string calldata institutionId) external view override returns (Attribute[] memory) {
        require(msg.sender == userAddress || msg.sender == institutions[institutionId].attributeAdmin, "Unauthorized access");
        return userAttributes[userAddress][institutionId];
    }

    function addEncryptData(string calldata dataId, string calldata encryptionPolicy) external override {
        require(dataRecords[dataId].dataTxHash == bytes32(0), "Data already exists");
        require(isValidEncryptionPolicy(encryptionPolicy), "Invalid encryption policy");
        require(users[msg.sender].status == ApprovalStatus.Approved, "User not approved");

        TxHashAccessor he = TxHashAccessor(0x00000000000000000000000000000000000000fa);
        bytes32 txHash = he.getHash();

        dataRecords[dataId] = DataRecord(msg.sender, txHash, encryptionPolicy);
        emit EncryptedDataAdded(dataId);
    }

    function getDataRecord(string calldata dataId) external view override returns (DataRecord memory) {
        return dataRecords[dataId];
    }

    function updateDataEncryptionPolicy(string calldata dataId, string calldata encryptionPolicy) external override {
        require(dataRecords[dataId].creator == msg.sender, "Only data creator can update");
        require(dataRecords[dataId].dataTxHash != bytes32(0), "Data not found");
        require(isValidEncryptionPolicy(encryptionPolicy), "Invalid encryption policy");

        TxHashAccessor he = TxHashAccessor(0x00000000000000000000000000000000000000fa);
        bytes32 txHash = he.getHash();

        dataRecords[dataId].encryptionPolicy = encryptionPolicy;
        dataRecords[dataId].dataTxHash = txHash;
    }

    function requestDecryptionKey(string calldata dataId) external override {
        require(dataRecords[dataId].dataTxHash != bytes32(0), "Data not found");
        require(users[msg.sender].status == ApprovalStatus.Approved, "User not approved");
        require(satisfiesPolicy(msg.sender, dataRecords[dataId].encryptionPolicy), "User does not satisfy the encryption policy");

        emit DecryptionKeyRequested(dataId, msg.sender, users[msg.sender].publicKey);
    }

    // 全局参数相关函数实现
    function getGlobalParameter() external view override returns (bytes memory) {
        return globalParameter;
    }

    // Helper functions
    function areAttributeIdsUnique(string[] memory attributeIds) internal pure returns (bool) {
        for (uint i = 0; i < attributeIds.length; i++) {
            for (uint j = i + 1; j < attributeIds.length; j++) {
                if (keccak256(bytes(attributeIds[i])) == keccak256(bytes(attributeIds[j]))) {
                    return false;
                }
            }
        }
        return true;
    }

    function areAttributeIdsValid(string memory institutionId, string[] memory attributeIds) internal view returns (bool) {
        string[] memory institutionAttributeIds = institutions[institutionId].attributeIds;
        for (uint i = 0; i < attributeIds.length; i++) {
            bool found = false;
            string[] memory parts = split(attributeIds[i], ":");
            if (parts.length != 2) return false;
            if (keccak256(bytes(parts[0])) != keccak256(bytes(institutionId))) {
                return false; // Attribute ID must be in the format institutionId:attributeId
            }
            for (uint j = 0; j < institutionAttributeIds.length; j++) {
                if (keccak256(bytes(parts[1])) == keccak256(bytes(institutionAttributeIds[j]))) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }
        return true;
    }

    function isValidEncryptionPolicy(string memory policy) internal view returns (bool) {
        string[] memory tokens = parsePolicy(policy);
        uint parenthesesCount = 0;
        bool expectOperator = false;

        for (uint i = 0; i < tokens.length; i++) {
            if (keccak256(bytes(tokens[i])) == keccak256(bytes("("))) {
                parenthesesCount++;
                expectOperator = false;
            } else if (keccak256(bytes(tokens[i])) == keccak256(bytes(")"))) {
                if (parenthesesCount == 0) return false;
                parenthesesCount--;
                expectOperator = true;
            } else if (keccak256(bytes(tokens[i])) == keccak256(bytes("AND")) || keccak256(bytes(tokens[i])) == keccak256(bytes("OR"))) {
                if (!expectOperator) return false;
                expectOperator = false;
            } else {
                if (expectOperator) return false;
                string[] memory parts = split(tokens[i], ":");
                if (parts.length != 2) return false;
                if (institutions[parts[0]].status != ApprovalStatus.Approved) return false;
                bool attributeFound = false;
                for (uint j = 0; j < institutions[parts[0]].attributeIds.length; j++) {
                    if (keccak256(bytes(institutions[parts[0]].attributeIds[j])) == keccak256(bytes(parts[1]))) {
                        attributeFound = true;
                        break;
                    }
                }
                if (!attributeFound) return false;
                expectOperator = true;
            }
        }

        return parenthesesCount == 0 && expectOperator;
    }

    function satisfiesPolicy(address user, string memory policy) internal view returns (bool) {
        string[] memory tokens = parsePolicy(policy);
        return evaluatePolicy(user, tokens, 0, tokens.length - 1);
    }

    function evaluatePolicy(address user, string[] memory tokens, uint start, uint end) internal view returns (bool) {
        if (start > end) return false;
        if (start == end) return evaluateAttribute(user, tokens[start]);

        uint parenthesesCount = 0;
        uint operatorIndex = type(uint).max;

        for (uint i = start; i <= end; i++) {
            if (keccak256(bytes(tokens[i])) == keccak256(bytes("("))) {
                parenthesesCount++;
            } else if (keccak256(bytes(tokens[i])) == keccak256(bytes(")"))) {
                parenthesesCount--;
            } else if (parenthesesCount == 0 && (keccak256(bytes(tokens[i])) == keccak256(bytes("AND")) || keccak256(bytes(tokens[i])) == keccak256(bytes("OR")))) {
                operatorIndex = i;
                break;
            }
        }

        if (operatorIndex != type(uint).max) {
            bool leftResult = evaluatePolicy(user, tokens, start, operatorIndex - 1);
            bool rightResult = evaluatePolicy(user, tokens, operatorIndex + 1, end);

            return keccak256(bytes(tokens[operatorIndex])) == keccak256(bytes("AND")) ? leftResult && rightResult : leftResult || rightResult;
        } else {
            return keccak256(bytes(tokens[start])) == keccak256(bytes("(")) ? evaluatePolicy(user, tokens, start + 1, end - 1) : false;
        }
    }

    function evaluateAttribute(address user, string memory attribute) internal view returns (bool) {
        string[] memory parts = split(attribute, ":");
        if (parts.length != 2) return false;

        Attribute[] storage attrs = userAttributes[user][parts[0]];
        for (uint i = 0; i < attrs.length; i++) {
            if (keccak256(bytes(attrs[i].id)) == keccak256(bytes(attribute)) && attrs[i].status == ApprovalStatus.Approved) {
                return true;
            }
        }
        return false;
    }

    function parsePolicy(string memory policy) internal pure returns (string[] memory) {
        string[] memory tokens = new string[](bytes(policy).length);
        uint tokenCount = 0;
        uint start = 0;
        bool inAttribute = false;

        for (uint i = 0; i < bytes(policy).length; i++) {
            if (bytes(policy)[i] == "(" || bytes(policy)[i] == ")") {
                if (inAttribute) {
                    tokens[tokenCount++] = substring(policy, start, i);
                    inAttribute = false;
                }
                tokens[tokenCount++] = substring(policy, i, i + 1);
                start = i + 1;
            } else if (bytes(policy)[i] == " ") {
                if (inAttribute) {
                    tokens[tokenCount++] = substring(policy, start, i);
                    inAttribute = false;
                }
                start = i + 1;
            } else {
                if (!inAttribute) {
                    inAttribute = true;
                    start = i;
                }
            }
        }

        if (inAttribute) {
            tokens[tokenCount++] = substring(policy, start, bytes(policy).length);
        }

        string[] memory result = new string[](tokenCount);
        for (uint i = 0; i < tokenCount; i++) {
            result[i] = tokens[i];
        }

        return result;
    }

    function substring(string memory str, uint startIndex, uint endIndex) internal pure returns (string memory) {
        bytes memory strBytes = bytes(str);
        bytes memory result = new bytes(endIndex - startIndex);
        for (uint i = startIndex; i < endIndex; i++) {
            result[i - startIndex] = strBytes[i];
        }
        return string(result);
    }

    function split(string memory _base, string memory _value) internal pure returns (string[] memory splitArr) {
        bytes memory _baseBytes = bytes(_base);

        uint _offset = 0;
        uint _splitsCount = 1;
        while (_offset < _baseBytes.length - 1) {
            int _limit = _indexOf(_baseBytes, _value, _offset);
            if (_limit == - 1)
                break;
            else {
                _splitsCount++;
                _offset = uint(_limit) + 1;
            }
        }

        splitArr = new string[](_splitsCount);

        _offset = 0;
        _splitsCount = 0;
        while (_offset < _baseBytes.length - 1) {

            int _limit = _indexOf(_baseBytes, _value, _offset);
            if (_limit == - 1) {
                _limit = int(_baseBytes.length);
            }

            string memory _tmp = new string(uint(_limit) - _offset);
            bytes memory _tmpBytes = bytes(_tmp);

            uint j = 0;
            for (uint i = _offset; i < uint(_limit); i++) {
                _tmpBytes[j++] = _baseBytes[i];
            }
            _offset = uint(_limit) + 1;
            splitArr[_splitsCount++] = string(_tmpBytes);
        }
        return splitArr;
    }

    function _indexOf(bytes memory _baseBytes, string memory _value, uint _offset) internal pure returns (int) {
        bytes memory _valueBytes = bytes(_value);

        assert(_valueBytes.length == 1);

        for (uint i = _offset; i < _baseBytes.length; i++) {
            if (_baseBytes[i] == _valueBytes[0]) {
                return int(i);
            }
        }

        return - 1;
    }
}

abstract contract TxHashAccessor {
    function getHash() public virtual returns (bytes32);
}