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
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}


// OpenZeppelin Contracts v4.4.0 (token/ERC721/IERC721Receiver.sol)

pragma solidity ^0.8.0;

/**
 * @title ERC721 token receiver interface
 * @dev Interface for any contract that wants to support safeTransfers
 * from ERC721 asset contracts.
 */
interface IERC721Receiver {
    /**
     * @dev Whenever an {IERC721} `tokenId` token is transferred to this contract via {IERC721-safeTransferFrom}
     * by `operator` from `from`, this function is called.
     *
     * It must return its Solidity selector to confirm the token transfer.
     * If any other value is returned or the interface is not implemented by the recipient, the transfer will be reverted.
     *
     * The selector can be obtained in Solidity with `IERC721.onERC721Received.selector`.
     */
    function onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes calldata data
    ) external returns (bytes4);
}


// OpenZeppelin Contracts v4.4.0 (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}




// OpenZeppelin Contracts v4.4.0 (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.0;

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}



pragma solidity ^0.8.0;


/**
 * @dev Implementation of the {IERC721Receiver} interface.
 *
 * Accepts all token transfers.
 * Make sure the contract is able to use its token with {IERC721-safeTransferFrom}, {IERC721-approve} or {IERC721-setApprovalForAll}.
 */
contract ERC721Holder is IERC721Receiver {
    /**
     * @dev See {IERC721Receiver-onERC721Received}.
     *
     * Always returns `IERC721Receiver.onERC721Received.selector`.
     */
    function onERC721Received(
        address,
        address,
        uint256,
        bytes memory
    ) public virtual override returns (bytes4) {
        return this.onERC721Received.selector;
    }
}



// OpenZeppelin Contracts v4.4.0 (utils/introspection/IERC165.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

pragma solidity ^0.8.0;

/**
 * @dev Required interface of an ERC721 compliant contract.
 */
interface IERC721 is IERC165 {
    /**
     * @dev Emitted when `tokenId` token is transferred from `from` to `to`.
     */
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables `approved` to manage the `tokenId` token.
     */
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables or disables (`approved`) `operator` to manage all of its assets.
     */
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    /**
     * @dev Returns the number of tokens in ``owner``'s account.
     */
    function balanceOf(address owner) external view returns (uint256 balance);

    /**
     * @dev Returns the owner of the `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function ownerOf(uint256 tokenId) external view returns (address owner);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`, checking first that contract recipients
     * are aware of the ERC721 protocol to prevent tokens from being forever locked.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be have been allowed to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Transfers `tokenId` token from `from` to `to`.
     *
     * WARNING: Usage of this method is discouraged, use {safeTransferFrom} whenever possible.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Gives permission to `to` to transfer `tokenId` token to another account.
     * The approval is cleared when the token is transferred.
     *
     * Only a single account can be approved at a time, so approving the zero address clears previous approvals.
     *
     * Requirements:
     *
     * - The caller must own the token or be an approved operator.
     * - `tokenId` must exist.
     *
     * Emits an {Approval} event.
     */
    function approve(address to, uint256 tokenId) external;

    /**
     * @dev Returns the account approved for `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function getApproved(uint256 tokenId) external view returns (address operator);

    /**
     * @dev Approve or remove `operator` as an operator for the caller.
     * Operators can call {transferFrom} or {safeTransferFrom} for any token owned by the caller.
     *
     * Requirements:
     *
     * - The `operator` cannot be the caller.
     *
     * Emits an {ApprovalForAll} event.
     */
    function setApprovalForAll(address operator, bool _approved) external;

    /**
     * @dev Returns if the `operator` is allowed to manage all of the assets of `owner`.
     *
     * See {setApprovalForAll}
     */
    function isApprovedForAll(address owner, address operator) external view returns (bool);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId,
        bytes calldata data
    ) external;
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


contract Utils {

    using Address for address;

    modifier onlyUser(){
        require(!address(msg.sender).isContract(), 'must be user');
        require(msg.sender == tx.origin, "proxy contract not allowed");
        _;
    }

    function calcStartSize(uint256 num, uint256 pageSize, uint256 currentPage) pure public returns (uint256 start, uint256 size) {
        if (num > 0) {
            start = (currentPage - 1) * pageSize;
            require(start < num, 'start error!');
            uint256 end = start + pageSize;
            size = pageSize;
            if (end > num) {
                end = num;
                size = end - start;
            }
        }
    }
}

pragma solidity ^0.8.0;

contract Exchange is Ownable, ERC721Holder,Utils {
    using SafeERC20 for IERC20;
    using Address for address;

    uint256 public auctionLength = 7 days;
    uint256 public auctionAdd = 15 minutes;
    uint16 public feeRate = 5;
    uint16 public feeTotal = 100;

    address public feeAddress;

    enum State {live, ended, redeemed}
    enum OrderAction {create, cancel, sell, buy}

    struct TokenInfo {
        address token;
        uint8 shift;
        bool available;
    }

    // auction
    struct Auction {
        uint256 tokenId;
        address seller;
        uint256 startPrice;
        uint256 price;
        address winner;
        uint256 startTime;
        uint256 auctionEnd;
        uint8 tokenKey;
        uint256 addLimit;
        State auctionState;
        uint256 buyoutPrice;
    }

    uint256[] public liveAuction;

    mapping(address => uint256[]) public auctionHistory;

    mapping(uint256 => uint256[]) public bids;

//    mapping(IERC20 => TokenInfo) public tokens;
    mapping(uint8 => TokenInfo) public tokens;
//     TokenInfo[] public tokens;

    // auction
    struct Order {
        address seller;
        uint256 tokenId;
        uint8 tokenKey;
        uint256 price;
        uint256 startTime;
    }

    Auction[] public auctions;

    Order[] public orders;

    IERC721 public nft;

    //66(tokenId)+ 150(price)+32(time) +8(type)  = 256
    mapping(address => uint256[]) public exchangeHistory;

    event AuctionOrder(uint256 indexed tokenId, address indexed seller, uint256 price);

    event Bid(uint256 indexed tokenId, address indexed buyer, uint256 price);

    event Won(uint256 indexed tokenId, address indexed buyer, uint256 price);

    event Redeem(uint256 indexed tokenId, address indexed redeemer);

    event Cash(uint256 indexed tokenId, address indexed owner, uint256 shares);

    event SellOrder(uint256 indexed tokenId, address indexed seller, uint256 price);

    event CancelOrder(uint256 indexed tokenId, address indexed seller);

    event Buy(uint256 indexed tokenId, address indexed buyer, uint256 price);

    event Fee(uint256 indexed tokenId, address indexed feer, uint256 price);

    event EmergencyToken(address token, address to, uint256 amount);
    event EmergencyTokenIds(address to, uint256[] tokenIds);

    constructor(address _nft, address feeAddress_) public {
        nft = IERC721(_nft);
        feeAddress = feeAddress_;
    }

    function setToken(uint8 tokenKey, address _token, bool _available, uint8 _shift) public onlyOwner {
        tokens[tokenKey] = TokenInfo({
        token: _token,
        shift : _shift,
        available : _available
        });
    }

    function setFeeRate(uint16 _feeRate) public onlyOwner{
        feeRate = _feeRate;
    }

    function setFeeAddress(address feeAddress_) public onlyOwner {
        feeAddress = feeAddress_;
    }

    function setAuctionLength(uint256 _auctionLength) public onlyOwner {
        auctionLength = _auctionLength;
    }

    function setAuctionAdd(uint256 _auctionAdd) public onlyOwner {
        auctionAdd = _auctionAdd;
    }

    function removeOrder(uint256 index) private {
        require(index < orders.length, 'removeOrder:error');
        orders[index] = orders[orders.length - 1];
        orders.pop();
    }

    function removeAuction(uint256 index) private {
        require(index < auctions.length, 'removeAuction:error');
        liveAuction[index] = liveAuction[liveAuction.length - 1];
        liveAuction.pop();
    }

    //66(tokenId)+ 150(price)+32(time) +8(type)  = 256
    function putHistory(uint256 tokenId, uint256 price, OrderAction action, address user) private {
        tokenId = (tokenId << 150) | price;
        tokenId = (tokenId << 32) | block.timestamp;
        tokenId = (tokenId << 8) | uint8(action);
        exchangeHistory[user].push(tokenId);
    }

    function sell(uint8 _tokenKey, uint256 tokenId, uint256 price) onlyUser external {
        TokenInfo storage token = tokens[_tokenKey];
        IERC20 token_ = IERC20(token.token);
        require(price < token_.totalSupply(), 'sell: price error!');
        require(token.available, 'launch: token error');
        nft.safeTransferFrom(msg.sender, address(this), tokenId);
        orders.push(Order({
        seller : msg.sender,
        tokenId : tokenId,
        tokenKey : _tokenKey,
        price : price,
        startTime : block.timestamp
        }));
        putHistory(tokenId, price, OrderAction.create, msg.sender);
        emit SellOrder(tokenId, msg.sender, price);
    }

    function cancelOrder(uint256 index) onlyUser external {
        require(index < orders.length, 'cancelOrder:index error');
        Order storage order = orders[index];
        require(order.seller == msg.sender);
        nft.safeTransferFrom(address(this), msg.sender, order.tokenId);
        putHistory(order.tokenId, order.price, OrderAction.cancel, msg.sender);
        removeOrder(index);
        emit CancelOrder(order.tokenId, msg.sender);
    }

    function buy(uint256 index, uint256 tokenId) onlyUser external {
        require(index < orders.length, 'buy:index error');
        Order storage order = orders[index];
        require(order.tokenId == tokenId, "buy:id error");
        TokenInfo storage token = tokens[order.tokenKey];
        require(token.available, 'token: token not available');
        uint256 userPrice = order.price - ((order.price * feeRate) / feeTotal);
        uint256 feePrice = order.price - userPrice;
        require((feePrice + userPrice) == order.price, 'token: order Amt error');
        IERC20 token_ = IERC20(token.token);
        token_.safeTransferFrom(msg.sender, order.seller, userPrice);
        token_.safeTransferFrom(msg.sender, feeAddress, feePrice);
        nft.safeTransferFrom(address(this), msg.sender, tokenId);
        putHistory(order.tokenId, order.price, OrderAction.buy, msg.sender);
        putHistory(order.tokenId, order.price, OrderAction.sell, order.seller);
        removeOrder(index);
        emit Fee(tokenId, feeAddress, feePrice);
        emit Buy(tokenId, msg.sender, userPrice);
    }

    function buyOut(uint256 index, uint256 tokenId) onlyUser external {
        require(index < auctions.length, 'buy:index error');
        Auction storage auction = auctions[index];
        require(auction.tokenId == tokenId, "buy:id error");
        TokenInfo storage token = tokens[auction.tokenKey];
        require(token.available, 'token: token not available');
        IERC20 token_ = IERC20(token.token);
        uint256 userPrice = auction.price - ((auction.price * feeRate) / feeTotal);
        uint256 feePrice = auction.price - userPrice;
        require((feePrice + userPrice) == auction.price, 'token: order Amt error');
        if (auction.winner != address(0)) {
            token_.safeTransfer(auction.winner, auction.price);
        }
        auction.price = auction.buyoutPrice;
        auction.winner = msg.sender;
        token_.safeTransferFrom(msg.sender, auction.seller, userPrice);
        token_.safeTransferFrom(msg.sender, feeAddress, feePrice);
        nft.safeTransferFrom(address(this), msg.sender, tokenId);
        auction.auctionState = State.ended;
        removeAuction(index);
        emit Fee(tokenId, feeAddress, feePrice);
        emit Won(tokenId, auction.winner, userPrice);
    }

    function launchAuction(uint256 tokenId, uint8 _tokenKey, uint256 _addLimit, uint256 initPrice, uint256 _buyoutPrice) onlyUser external {
        TokenInfo storage token = tokens[_tokenKey];
        require(token.available, 'token: token not available');
        IERC20 token_ = IERC20(token.token);
        require(initPrice < token_.totalSupply(), 'launch: initPrice error!');
        nft.safeTransferFrom(msg.sender, address(this), tokenId);
        auctions.push(
            Auction({
                tokenId: tokenId,
                seller: msg.sender,
                startPrice: initPrice,
                price: initPrice,
                winner: address(0),
                startTime: block.timestamp,
                auctionEnd: block.timestamp + auctionLength,
                tokenKey: _tokenKey,
                addLimit: _addLimit,
                auctionState: State.live,
                buyoutPrice: _buyoutPrice
                })
        );
        auctionHistory[msg.sender].push(auctions.length - 1);
        liveAuction.push(auctions.length - 1);
        emit AuctionOrder(tokenId, msg.sender, initPrice);
    }

    function fillAuctionHistory(uint256 index) private {
        if (auctions[index].seller == msg.sender) {
            return;
        }
        uint256 len = auctionHistory[msg.sender].length;
        if (len == 0) {
            auctionHistory[msg.sender].push(index);
        } else {
            uint256 count = 0;
            for (uint256 i = len; i > 0 && count < 10; i--) {
                if (auctionHistory[msg.sender][i - 1] == index) {
                    return;
                }
                count++;
            }
            auctionHistory[msg.sender].push(index);
        }
    }

    function needFillAuctionHistory(uint256 index) public returns (bool ) {
        if (index >= auctions.length) {
            return false;
        }
        Auction storage auction = auctions[index];
        if (index >= auctionHistory[auction.seller].length) {
            return false;
        }
        if (index >= auctionHistory[auction.seller][index]) {
            return true;
        }
        return false;
    }

    function bid(uint256 index, uint256 tokenId, uint256 price, bool history) onlyUser external {
        require(index < auctions.length, 'bid:index error');
        Auction storage auction = auctions[index];
        require(auction.tokenId == tokenId, "bid:id error");
        require(block.timestamp < auction.auctionEnd, "bid:auction ended");
        require(auction.price < price, "bid:price error");
        require(auction.auctionState == State.live, 'bid:state error');
        fillAuctionHistory(index);
        //价格浮动检查
        //        uint256 increase = ISettings(settings).minBidIncrease() + 1000;
        //        require(msg.value * 1000 <= livePrice * increase, "bid:too high bid");

        // If bid is within 15 minutes of auction end, extend auction
        if (auction.auctionEnd - block.timestamp <= auctionAdd) {
            auction.auctionEnd += auctionAdd;
        }
        TokenInfo storage token = tokens[auction.tokenKey];
        require(token.available, 'token: token not available');
        IERC20 token_ = IERC20(token.token);
        uint256 before_ = token_.balanceOf(address(this));
        token_.safeTransferFrom(msg.sender, address(this), price);
        uint256 after_ = token_.balanceOf(address(this));
        uint256 diff = after_ - before_;
        require(diff > auction.addLimit, 'bid:diff error!');
        if (auction.winner != address(0)) {
            token_.safeTransfer(auction.winner, auction.price);
        }
        auction.price = price;
        auction.winner = msg.sender;
        uint256 history = (uint256(uint160(msg.sender)) << 96) | (price / tokens[auction.tokenKey].shift);
        bids[index].push(history);
        emit Bid(tokenId, msg.sender, price);
        if (price >= auction.buyoutPrice) {
            uint256 userPrice = auction.price - ((auction.price * feeRate) / feeTotal);
            uint256 feePrice = auction.price - userPrice;
            require((feePrice + userPrice) == auction.price, 'token: order Amt error');
            token_.safeTransferFrom(address(this), auction.seller, userPrice);
            nft.safeTransferFrom(address(this), msg.sender, tokenId);
            auction.auctionState = State.ended;
            removeAuction(index);
            emit Fee(tokenId, feeAddress, feePrice);
            emit Won(tokenId, auction.winner, auction.price);
        }
    }

    function end(uint256 index, uint256 tokenId) onlyUser external {
        require(index < auctions.length, 'end:index error');
        Auction storage auction = auctions[index];
        require(auction.auctionState == State.live, 'end:state error');
        require(auction.tokenId == tokenId, "end:id error");
        require(block.timestamp >= auction.auctionEnd, "end:auction live");

        uint256 userPrice = auction.price - ((auction.price * feeRate) / feeTotal);
        uint256 feePrice = auction.price - userPrice;
        require((feePrice + userPrice) == auction.price, 'token: order Amt error');
        // transfer erc721 to winner
        TokenInfo storage token = tokens[auction.tokenKey];
        require(token.available, 'token: token not available');
        IERC20 token_ = IERC20(token.token);
        token_.safeTransferFrom(msg.sender, auction.seller, userPrice);
        token_.safeTransferFrom(msg.sender, feeAddress, feePrice);
        nft.safeTransferFrom(address(this), auction.winner, auction.tokenId);
        auction.auctionState = State.ended;
        removeAuction(index);
        emit Fee(tokenId, feeAddress, feePrice);
        emit Won(tokenId, auction.winner, auction.price);
    }

    function redeem(uint256 index) onlyUser external {
        require(index < auctions.length, 'redeem:index error');
        Auction storage auction = auctions[index];
        require(auction.auctionState == State.live, 'redeem:state error');
        require(auction.winner == address(0), "redeem:state error");
        require(auction.seller == msg.sender, "redeem:user error");
        // transfer erc721 to redeemer
        nft.safeTransferFrom(address(this), auction.seller, auction.tokenId);
        auction.auctionState = State.redeemed;
        removeAuction(index);
        emit Redeem(auction.tokenId, auction.seller);
    }

    function getOrders(uint256 pageSize, uint256 currentPage) view public returns (Order[] memory result){
        uint256 start;
        uint256 size;
        (start, size) = calcStartSize(orders.length, pageSize, currentPage);
        result = new Order[](size);
        for (uint i = 0; i < size; i++) {
            result[i] = orders[start + i];
        }
    }

    function getAuctions(uint256 pageSize, uint256 currentPage) view public returns (Auction[] memory result){
        uint256 start;
        uint256 size;
        (start, size) = calcStartSize(auctions.length, pageSize, currentPage);
        result = new Auction[](size);
        for (uint i = 0; i < size; i++) {
            result[i] = auctions[start + i];
        }
    }

    function getLiveAuctions(uint256 pageSize, uint256 currentPage) view public returns
        (Auction[] memory result, uint256[]  memory auctionIndex, uint256[] memory liveIndex){
        uint256 start;
        uint256 size;
        (start, size) = calcStartSize(liveAuction.length, pageSize, currentPage);
        liveIndex = new uint256[](size);
        auctionIndex = new uint256[](size);
        result = new Auction[](size);
        for (uint i = 0; i < size; i++) {
            result[i] = auctions[start + i];
            auctionIndex[i] = start + i;
            liveIndex[i] = start + i;
        }
    }

    function getAuctionLength() view public returns (uint256 all, uint256 live){
        all = auctions.length;
        live = liveAuction.length;
    }

    function getOrdersLength() view public returns (uint256){
        return orders.length;
    }

    function getAuction(uint256 index) view public returns (Auction memory){
        return auctions[index];
    }

    function getOrder(uint256 index) view public returns (Order memory){
        return orders[index];
    }

    function getAuctionBids(uint256 index, uint256 pageSize, uint256 currentPage) view public returns (uint256[] memory result){
        uint256 start;
        uint256 size;
        (start, size) = calcStartSize(bids[index].length, pageSize, currentPage);
        result = new uint256[](size);
        for (uint i = 0; i < size; i++) {
            result[i] = bids[index][start + i];
        }
    }

    function getUserAuctions(address user, uint256 pageSize, uint256 currentPage) view public returns (uint256[] memory result){
        uint256 start;
        uint256 size;
        (start, size) = calcStartSize(auctionHistory[user].length, pageSize, currentPage);
        result = new uint256[](size);
        for (uint i = 0; i < size; i++) {
            result[i] = auctionHistory[user][start + i];
        }
    }

    function getExchangeActions(address user, uint256 pageSize, uint256 currentPage) view public returns (uint256[] memory result){
        uint256 start;
        uint256 size;
        (start, size) = calcStartSize(exchangeHistory[user].length, pageSize, currentPage);
        result = new uint256[](size);
        for (uint i = 0; i < size; i++) {
            result[i] = exchangeHistory[user][start + i];
        }
    }

    function emergencyToken(address token_, address to_, uint256 amount_) onlyOwner external {
        IERC20(token_).transfer(to_, amount_);
        emit EmergencyToken(token_, to_, amount_);
    }

    function emergencyTokenIds(address to_, uint256[] memory tokenIds) onlyOwner external {
        for (uint i = 0; i < tokenIds.length; i++) {
            nft.safeTransferFrom(address(this), to_, tokenIds[i]);
        }
        emit EmergencyTokenIds(to_, tokenIds);
    }
}
