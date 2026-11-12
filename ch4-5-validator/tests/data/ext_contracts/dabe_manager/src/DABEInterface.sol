// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface DABEInterface {
    // 结构体定义
    enum ApprovalStatus { NotRegistered, Pending, Approved, Rejected }

    struct Attribute {
        string id;    // 属性id (机构id+属性字符串)
        ApprovalStatus status; // 属性的审核状态
    }

    struct DataRecord {
        address creator;         // 数据创建者
        bytes32 dataTxHash;      // 数据所在的交易Hash（extra）
        string encryptionPolicy; // 加密策略
    }

    struct Institution { // 机构
        string id;
        address creator;  // 机构创建者
        ApprovalStatus status;
        address attributeAdmin;
        string[] attributeIds;   // 机构属性列表, 属性为属性字符串
        bytes pk; // 机构公钥
    }

    struct User { // 用户
        address userAddress;
        ApprovalStatus status; // 复核状态
        bytes publicKey;       // 用户公钥
    }

    // 事件定义

    // 机构注册事件, 机构注册时触发，可以由机构管理员订阅
    event InstitutionRegistered(string institutionId, string[] attributeIds);
    // 机构审核状态变更事件
    event InstitutionStatusChanged(string institutionId, ApprovalStatus newStatus);
    // 用户注册事件, 用户注册时触发，可以由平台管理员订阅
    event UserRegistered(address userAddress, bytes publicKey);
    // 用户属性添加事件, 用户属性注册/添加时触发，可以由机构订阅
    event UserAttributeAdded(address userAddress, string institutionId, string[] attributeIds);
    // 复核状态变更事件
    event UserStatusChanged(address userAddress, ApprovalStatus newStatus);
    // 用户属性审核状态变更事件
    event UserAttributeStatusChanged(address userAddress, string institutionId, string[] attributeIds, ApprovalStatus newStatus);
    // 新增加密数据事件, 加密数据添加时触发，为预留事件
    event EncryptedDataAdded(string dataId);
    // 解密密钥请求事件, 用户请求解密密钥时触发，可以由机构订阅
    event DecryptionKeyRequested(string dataId, address userAddress, bytes userPubKey);

    // 机构相关函数
    function registerInstitution(string calldata institutionId, address attributeAdmin, string[] memory attributeIds, bytes calldata pk) external;
    function updateInstitutionInfo(string calldata institutionId, address attributeAdmin, string[] memory attributeIds, bytes calldata pk) external;
    function updateInstitutionStatus(string calldata institutionId, ApprovalStatus newStatus) external;
    function getInstitutionInfo(string calldata institutionId) external view returns (Institution memory);

    // 用户相关函数
    function registerUser(bytes calldata publicKey) external;
    function addUserAttribute(string calldata institutionId, string[] memory attributeIds) external;
    function updateUserStatus(address userAddress, ApprovalStatus newStatus) external;
    function updateUserAttributeStatus(address userAddress, string calldata institutionId, string[] memory attributeIds, ApprovalStatus newStatus) external;
    function getUserPublicKey(address userAddress) external view returns (bytes memory);
    function getUserAttributes(address userAddress, string calldata institutionId) external view returns (Attribute[] memory);

    // 数据相关函数
    function addEncryptData(string calldata dataId, string calldata encryptionPolicy) external;
    function getDataRecord(string calldata dataId) external view returns (DataRecord memory);
    function updateDataEncryptionPolicy(string calldata dataId, string calldata encryptionPolicy) external;

    // 解密请求相关函数
    function requestDecryptionKey(string calldata dataId) external;

    // 全局参数相关函数
    function getGlobalParameter() external view returns (bytes memory);
}