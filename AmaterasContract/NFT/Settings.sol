// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.0 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}


pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

pragma solidity ^0.8.0;

interface ISettings {

    function getNewCard() external returns (uint8, uint8);

    function getUrCard(uint) external;

    function usdt() view external returns (address);

    function getGodSource(uint8) view external returns (uint16[] memory);

    function godQuality() view external returns (uint8);

    function toInviter() view external returns (uint256);

    function toDividendsPool() view external returns (uint256);

    function toBonusesPool() view external returns (uint256);

    function toDev() view external returns (uint256);

    function defaultInviter() view external returns (address);

    function dev() view external returns (address);

    function mat() view external returns (address);

    function stakePower(uint8) view external returns (uint256);

    function beInviterAmt() view external returns (uint256);

    function bonusesSwapRate(uint8) view external returns (uint256);

    function dividendPower(uint8) view external returns (uint256);

    function boxPrice() view external returns (uint256);

    function priceStep() view external returns (uint256);

    function urPrice() view external returns (uint256);


}


contract Settings is Ownable, ISettings {
    address public factory;

    uint256 public override boxPrice = 5 * (10 ** 18);

    uint256 public override  priceStep = 5 * (10 ** 12);

    uint256 public override  urPrice = 1500 * (10 ** 18);

    uint private randomNonce;

    address public  override usdt;

    uint8 public  override godQuality = uint8(9);

    uint256 public override toInviter = 1000;

    uint256 public override toDividendsPool = 2700;

    uint256 public override toBonusesPool = 2700;

    uint256 public override beInviterAmt = 100 * (10 ** 18);

    uint256 public override toDev = 3600;

    address  public override defaultInviter;

    address public override dev;

    address public override mat;

    uint256[5] urCount = [0, 0, 0, 0, 0];

    uint256 public maxUrCount = 100;

    bool public urActive = true;


    mapping(uint8 => uint256) public override stakePower;
    mapping(uint8 => uint256) public override bonusesSwapRate;
    mapping(uint8 => uint256) public override dividendPower;
    mapping(uint8 => uint16[]) public godSource;

    function setFactory(address _factory) public onlyOwner {
        factory = _factory;
    }

    function setMat(address _mat) public onlyOwner {
        mat = _mat;
    }

    function setDev(address _dev) public onlyOwner {
        dev = _dev;
    }

    function setMaxUrCount(uint256 _maxUrCount) public onlyOwner {
        maxUrCount = _maxUrCount;
    }

    modifier onlyFactory() {
        require(factory == msg.sender, "Settings: only factory");
        _;
    }

    constructor(address _usdt, address _mat) public {
        usdt = _usdt;
        mat = _mat;
        defaultInviter = msg.sender;
        dev = msg.sender;

        //stakePower
        stakePower[0] = 0;
        stakePower[1] = 100;
        stakePower[2] = 228;
        stakePower[3] = 430;
        stakePower[4] = 1900;
        stakePower[5] = 18900;

        //bonusesSwapRate
        bonusesSwapRate[0] = 1;
        bonusesSwapRate[1] = 5;
        bonusesSwapRate[2] = 5;
        bonusesSwapRate[3] = 5;
        bonusesSwapRate[4] = 1;
        bonusesSwapRate[5] = 5;
        bonusesSwapRate[6] = 5;
        bonusesSwapRate[7] = 5;
        bonusesSwapRate[8] = 5;
        bonusesSwapRate[9] = 5;
        bonusesSwapRate[10] = 5;
        bonusesSwapRate[11] = 5;
        bonusesSwapRate[12] = 5;
        bonusesSwapRate[13] = 9;
        bonusesSwapRate[14] = 5;
        bonusesSwapRate[15] = 13;
        bonusesSwapRate[16] = 9;
        bonusesSwapRate[17] = 18;

        dividendPower[0] = 1;
        dividendPower[1] = 2;
        dividendPower[2] = 2;
        dividendPower[3] = 2;
        dividendPower[4] = 1;
        dividendPower[5] = 2;
        dividendPower[6] = 2;
        dividendPower[7] = 2;
        dividendPower[8] = 2;
        dividendPower[9] = 2;
        dividendPower[10] = 2;
        dividendPower[11] = 2;
        dividendPower[12] = 2;
        dividendPower[13] = 3;
        dividendPower[14] = 2;
        dividendPower[15] = 4;
        dividendPower[16] = 3;
        dividendPower[17] = 5;

        godSource[0] = [uint16((4 << 8) | 2), uint16((1 << 8) | 0), uint16((1 << 8) | 1), uint16((3 << 8) | 3), uint16((5 << 8) | 2)];
        godSource[1] = [uint16((1 << 8) | 2), uint16((1 << 8) | 3), uint16((2 << 8) | 0), uint16((3 << 8) | 4), uint16((2 << 8) | 36), uint16((5 << 8) | 3)];
        godSource[2] = [uint16((3 << 8) | 5), uint16((2 << 8) | 1), uint16((1 << 8) | 4), uint16((2 << 8) | 17), uint16((2 << 8) | 22), uint16((2 << 8) | 37), uint16((5 << 8) | 3)];
        godSource[3] = [uint16((3 << 8) | 6), uint16((2 << 8) | 2), uint16((1 << 8) | 5), uint16((2 << 8) | 16), uint16((3 << 8) | 28), uint16((2 << 8) | 38), uint16((5 << 8) | 2)];
        godSource[4] = [uint16((1 << 8) | 5), uint16((3 << 8) | 7), uint16((2 << 8) | 43), uint16((5 << 8) | 0)];
        godSource[5] = [uint16((3 << 8) | 8), uint16((2 << 8) | 3), uint16((1 << 8) | 6), uint16((1 << 8) | 7), uint16((2 << 8) | 39), uint16((5 << 8) | 1)];
        godSource[6] = [uint16((3 << 8) | 9), uint16((1 << 8) | 8), uint16((1 << 8) | 9), uint16((2 << 8) | 4), uint16((2 << 8) | 40), uint16((5 << 8) | 0)];
        godSource[7] = [uint16((3 << 8) | 10), uint16((3 << 8) | 11), uint16((3 << 8) | 12), uint16((1 << 8) | 10), uint16((2 << 8) | 5), uint16((2 << 8) | 41), uint16((5 << 8) | 3)];
        godSource[8] = [uint16((3 << 8) | 13), uint16((2 << 8) | 6), uint16((2 << 8) | 42), uint16((3 << 8) | 39), uint16((3 << 8) | 40), uint16((5 << 8) | 2)];
        godSource[9] = [uint16((3 << 8) | 14), uint16((2 << 8) | 16), uint16((3 << 8) | 32), uint16((3 << 8) | 41), uint16((3 << 8) | 42), uint16((5 << 8) | 3)];
        godSource[10] = [uint16((3 << 8) | 15), uint16((2 << 8) | 7), uint16((1 << 8) | 11), uint16((3 << 8) | 29), uint16((3 << 8) | 33), uint16((3 << 8) | 45), uint16((5 << 8) | 1)];
        godSource[11] = [uint16((3 << 8) | 16), uint16((2 << 8) | 8), uint16((1 << 8) | 12), uint16((3 << 8) | 34), uint16((5 << 8) | 0)];
        godSource[12] = [uint16((2 << 8) | 9), uint16((2 << 8) | 10), uint16((3 << 8) | 17), uint16((2 << 8) | 34), uint16((1 << 8) | 29), uint16((5 << 8) | 2)];
        godSource[13] = [uint16((4 << 8) | 3), uint16((3 << 8) | 18), uint16((3 << 8) | 19), uint16((2 << 8) | 29), uint16((4 << 8) | 9), uint16((3 << 8) | 38), uint16((3 << 8) | 46), uint16((5 << 8) | 2)];
        godSource[14] = [uint16((3 << 8) | 20), uint16((2 << 8) | 11), uint16((2 << 8) | 12), uint16((3 << 8) | 24), uint16((3 << 8) | 25), uint16((5 << 8) | 3)];
        godSource[15] = [uint16((3 << 8) | 21), uint16((2 << 8) | 13), uint16((4 << 8) | 4), uint16((4 << 8) | 5), uint16((3 << 8) | 24), uint16((3 << 8) | 25), uint16((5 << 8) | 1)];
        godSource[16] = [uint16((1 << 8) | 13), uint16((2 << 8) | 16), uint16((3 << 8) | 27), uint16((3 << 8) | 28), uint16((4 << 8) | 6), uint16((5 << 8) | 3)];
        godSource[17] = [uint16((4 << 8) | 7), uint16((4 << 8) | 8), uint16((4 << 8) | 9), uint16((4 << 8) | 10), uint16((2 << 8) | 35), uint16((5 << 8) | 4)];
    }

    uint constant private  maxRandom = 10 ** 9;

//    function setUrActive(bool urActive_) onlyOnwer {
//        urActive = urActive_;
//    }

    function getUrInfo() public view returns (uint256[5] memory) {
        return urCount;
    }

    function getNFTInfo(uint256 random) private pure returns (uint8 quality, uint8 index){
        if (random < 3417282) {
            quality = uint8(5);
            index = uint8(random % 5);
        } else if (random < 33314764) {
            quality = uint8(4);
            index = uint8(random % 12);
        } else if (random < 162870517) {
            quality = uint8(3);
            index = uint8(random % 47);
        } else if (random < 412016196) {
            quality = uint8(2);
            index = uint8(random % 64);
        } else if (random < 980068345) {
            quality = uint8(1);
            index = uint8(random % 33);
        } else {
            quality = 0;
            index = 0;
        }
    }

    function randomIndex() private returns (uint) {
        randomNonce++;
        return uint(keccak256(abi.encodePacked(randomNonce, msg.sender, block.difficulty, block.timestamp))) % maxRandom;
    }

    function getNewCard() public override onlyFactory returns (uint8 quality, uint8 index){
        uint random = randomIndex();
        (quality, index) = getNFTInfo(random);
    }

    function getUrCard(uint256 index) public override onlyFactory {
        require(urCount[index] < maxUrCount, 'no left');
        urCount[index]++;
    }

    function getGodSource(uint8 targetGod) public view override returns (uint16[] memory result){
        return godSource[targetGod];
    }
}
