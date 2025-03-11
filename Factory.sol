// SPDX-License-Identifier: MIT
// File: SmartContracts/interface/IERC20.sol

pragma solidity ^0.8.9;

interface IERC20 {
    
    function totalSupply() external view returns(uint256);

    function balanceOf(address account) external view returns(uint256);
    
    function transfer(address recipient, uint256 amount) external returns(bool);

    function allowance(address owner, address spender) external view returns(uint256);

    function approve(address spender, uint256 amount) external returns(bool);

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns(bool);
        event Transfer(address indexed from, address indexed to, uint256 value);
        event Approval(address indexed owner, address indexed spender, uint256 value);
}
// File: SmartContracts/context/Context.sol


pragma solidity ^0.8.9;

abstract contract Context {
    function _msgSender() internal view virtual returns(address) {
        return msg.sender;
    }
}
// File: SmartContracts/contracts/Ownable.sol


pragma solidity ^0.8.9;


contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns(address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }
    
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}
// File: SmartContracts/interface/IUniswapV2Pair.sol


pragma solidity ^0.8.9;

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}
// File: SmartContracts/lib/Address.sol


pragma solidity ^0.8.9;

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
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
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

// File: SmartContracts/lib/SafeERC20.sol


pragma solidity ^0.8.9;



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

// File: SmartContracts/interface/IERC20Metadata.sol


pragma solidity ^0.8.9;


interface IERC20Metadata is IERC20 {
    function name() external view returns(string memory);

    function symbol() external view returns(string memory);

    function decimals() external view returns(uint8);
}
// File: SmartContracts/lib/SafeMath.sol


pragma solidity ^0.8.9;

library SafeMath {
   
    function add(uint256 a, uint256 b) internal pure returns(uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    function sub(uint256 a, uint256 b) internal pure returns(uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

   
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns(uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;
        return c;
    }

    function mul(uint256 a, uint256 b) internal pure returns(uint256) {
    
        if (a == 0) {
            return 0;
        }
 
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    function div(uint256 a, uint256 b) internal pure returns(uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns(uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold
        return c;
    }
}
// File: SmartContracts/contracts/ERC20.sol


pragma solidity ^0.8.9;




 
contract ERC20 is Context, IERC20, IERC20Metadata {
    using SafeMath for uint256;

    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;
 
    uint256 private _totalSupply;
 
    string _name;
    string _symbol;
    uint8 _decimals;

    constructor(string memory name_, string memory symbol_, uint8 decimals_) {
        _name = name_;
        _symbol = symbol_;
        _decimals = decimals_;
    }

    
    function name() public view virtual override returns(string memory) {
        return _name;
    }

   
    function symbol() public view virtual override returns(string memory) {
        return _symbol;
    }

    
    function decimals() public view virtual override returns(uint8) {
        return _decimals;
    }

   
    function totalSupply() public view virtual override returns(uint256) {
        return _totalSupply;
    }

    
    function balanceOf(address account) public view virtual override returns(uint256) {
        return _balances[account];
    }

    
    function transfer(address recipient, uint256 amount) public virtual override returns(bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    
    function allowance(address owner, address spender) public view virtual override returns(uint256) {
        return _allowances[owner][spender];
    }

    
    function approve(address spender, uint256 amount) public virtual override returns(bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns(bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }
    
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns(bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }
    
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns(bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased cannot be below zero"));
        return true;
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual {
        
        _balances[sender] = _balances[sender].sub(amount, "ERC20: transfer amount exceeds balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }

    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

}
// File: SmartContracts/contracts/Coin.sol


pragma solidity ^0.8.9;

contract Coin is ERC20, Ownable {
    using SafeMath for uint256;
    // Description 
    string public _description;
    address public creator;
    uint256 public createdTs;
    uint256 public lockPeriod;
    constructor(
        address wallet,
        address _creator,
        string [] memory tokenDatas,
        uint256 supply,
        uint8 decimals,
        uint256 _lockPeriod
                ) ERC20(tokenDatas[0], tokenDatas[1], decimals) {
        // set owner
        transferOwnership(msg.sender);

        // name
        _name = tokenDatas[0];
        _symbol = tokenDatas[1];
        _description = tokenDatas[2];
        // uint256 totalSupply = supply * (10 ** decimals);
        _mint(wallet, supply * (10 ** decimals));
        creator = _creator;
        createdTs = block.timestamp;
        lockPeriod = _lockPeriod;
    }

    receive() external payable {
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
        
    ) internal override {
        if(sender == creator) {
            require(block.timestamp > createdTs + lockPeriod, "Can't send within lock period");
        }
        if (amount == 0) {
            super._transfer(sender, recipient, 0);
            return;
        }
        super._transfer(sender, recipient, amount);
        // if owner is not address 0 means this is not launched
        if (owner() != address(0)) {
            // safuhub token - can't send tokens to pair before launch
            require(
                // check if to is a contract
                !_isContract(recipient) || sender == owner() || recipient == owner(),
                "Can't send tokens to contracts before launch"
            );
        }
    }

    function _isContract(address _addr) private view returns (bool) {
        uint32 size;
        assembly {
            size := extcodesize(_addr)
        }
        return (size > 0);
    }
}
// File: SmartContracts/interface/IUniswapV2Router01.sol


pragma solidity ^0.8.9;

interface IUniswapV2Router01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
}


// File: SmartContracts/abstract/ReentrancyGuard.sol
pragma solidity ^0.8.9;

abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}
// File: SmartContracts/interface/IFactoryContract.sol


pragma solidity ^0.8.9;

interface FactoryContract {
    function devWallet() external view returns(address);
    function feeAmount() external view returns(uint256);
    function mainFee() external view returns(uint8);
    function bondingCurve() external view returns(uint256);
    function WethPrice() external view returns(uint256);
    function bondingLimit() external view returns(uint256);
    function updateContributors(address _user, address _blackPump) external ;
}
// File: SmartContracts/contracts/SafuHub.sol


pragma solidity ^0.8.9;

struct PumpData {
    uint256 tokenAmount;
    uint256 ethAmount;
    uint256 virtualEthLp;
    uint256 virtualTokenLp;
    uint256 k;
}

struct AddressData {
    address coinAddr;
    address factoryAddr;
    address dexRouter;
}

contract SafuHub is Ownable, ReentrancyGuard {
    using SafeERC20 for IERC20;
    address public token;
    address public router;
    uint256 public tokenStartPrice;
    uint256 public virtualTokenLp;  // 1073 * (10 ** 9) amounts
    uint256 public virtualEthLp;
    uint256 public realTokenLp = 2 * (10 ** 29);    // 20% 10**12 18 decimal
    uint256 public realEthLp;
    uint256 public total = 10 ** 30; // 10 ** 12
    uint256 public k;
    bool public lpCreated;
    uint256 public startTimestamp;
    uint8 public maxBuy;

    // Fun Information
    string public name;
    string public info;
    string public symbol;
    string public website;
    string public twitter;
    string public telegram;
    string public discord;

    struct TokenPriceData {
        uint256 time;
        uint256 open;
        uint256 close;
        uint256 amount;
    }
    TokenPriceData[] internal tokenPriceDatas;
    
    mapping(address => mapping(address =>bool)) public contributorSet;

    mapping(address => uint256) public refAmounts;
    uint16 public  refCount;
    address[] public refAddresses;
    uint256 public totalRefAmounts;

    uint256 public volume;

    FactoryContract public factoryContract;

    receive() external payable {
    }

    constructor(
        address wallet,
        string [] memory tokenDatas,
        uint8 maxBuyAmount,
        AddressData memory _addresses,
        PumpData memory _otherDatas
    ){
        virtualEthLp = _otherDatas.virtualEthLp + _otherDatas.ethAmount;
        virtualTokenLp = _otherDatas.virtualTokenLp - _otherDatas.tokenAmount;
        k = _otherDatas.k;
        tokenStartPrice = _otherDatas.virtualEthLp * 10 ** 15 / _otherDatas.virtualTokenLp;
        router = _addresses.dexRouter;
        transferOwnership(wallet);
        token = _addresses.coinAddr;
        maxBuy = maxBuyAmount;
        name = tokenDatas[0];
        symbol = tokenDatas[1];
        info = tokenDatas[2];
        website = tokenDatas[3];
        twitter = tokenDatas[4];
        telegram = tokenDatas[5];
        discord = tokenDatas[6];
        factoryContract = FactoryContract(_addresses.factoryAddr);
        startTimestamp = block.timestamp;
        tokenPriceDatas.push(TokenPriceData(startTimestamp, tokenStartPrice, currentTokenPrice(), _otherDatas.ethAmount));
        volume = _otherDatas.ethAmount;
    }

    modifier onlyLive {
        require(lpCreated == false);
        _;
    }

    function buyToken(address _ref) external  payable onlyLive nonReentrant {
        uint256 openPrice = currentTokenPrice();
        uint8 mainFee = FactoryContract(factoryContract).mainFee();
        uint256 amounts = tokenAmount(msg.value);
        uint256 feeAmount = msg.value * mainFee / 100;
        uint256 sendingAmount = msg.value - feeAmount;

        if (_ref != address(0) && _ref != msg.sender)
        {
            uint256 referFee = feeAmount / 2;
            feeAmount -= referFee;
            payable(_ref).transfer(referFee);
            if(refAmounts[_ref] == 0){
                refCount ++;
                refAddresses.push(_ref);
            }
            refAmounts[_ref] += referFee;
            totalRefAmounts += referFee;
        }

        address feeAddress = FactoryContract(factoryContract).devWallet();
        payable(feeAddress).transfer(feeAmount * 7 / 10);       // 70% admin
        payable(owner()).transfer(feeAmount * 3 / 10);          // 30% owner
        uint256 tokenBalance = IERC20(token).balanceOf(msg.sender);
        require(amounts + tokenBalance < total * maxBuy / 100, "Exceed max wallet amount");
        virtualTokenLp -= amounts;
        virtualEthLp += sendingAmount;
        realEthLp += sendingAmount;
        volume += sendingAmount;
        IERC20(token).transfer(msg.sender, amounts);

        tokenPriceDatas.push(TokenPriceData(block.timestamp, openPrice, currentTokenPrice(), sendingAmount));
        uint256 bondingBalance = address(this).balance;
        uint256 bondingLimit = FactoryContract(factoryContract).bondingLimit();
        if(bondingLimit <= bondingBalance){
            finalize();
        }

        if(contributorSet[msg.sender][address(this)] == false)
        {
            FactoryContract(factoryContract).updateContributors(msg.sender, address(this));
            contributorSet[msg.sender][address(this)] = true;
        }
    }

    function sellToken(uint256 _amount, address _ref) external onlyLive nonReentrant {
        uint256 openPrice = currentTokenPrice();
        require(_amount < total * maxBuy / 100, "Exceed max wallet amount");
        uint8 mainFee = FactoryContract(factoryContract).mainFee();
        address feeAddress = FactoryContract(factoryContract).devWallet();
        uint256 ethOutAmount = ethAmount(_amount);
        uint256 feeAmount = ethOutAmount * mainFee / 100;
        uint256 sendingAmount = ethOutAmount - feeAmount;
        if(_ref != address(0) && _ref != msg.sender)
        {
            uint256 referFee = feeAmount / 2;
            feeAmount -= referFee;
            payable(_ref).transfer(referFee);
            if(refAmounts[_ref] == 0){
                refCount ++;
                refAddresses.push(_ref);
            }
            refAmounts[_ref] += referFee;
            totalRefAmounts += referFee;
        }
        payable(feeAddress).transfer(feeAmount * 7 / 10);
        payable(owner()).transfer(feeAmount * 3 / 10);
        payable(msg.sender).transfer(sendingAmount);
        virtualTokenLp += _amount;
        virtualEthLp -= ethOutAmount;
        realEthLp -= sendingAmount;
        volume += sendingAmount;
        IERC20(token).transferFrom(msg.sender, address(this), _amount);
        tokenPriceDatas.push(TokenPriceData(block.timestamp, openPrice, currentTokenPrice(), sendingAmount));
    }

    function tokenAmount(uint256 _ethAmount) internal view returns(uint256) {
        uint256 newEthAmount = virtualEthLp + _ethAmount;
        uint256 newTokenAmount = k / newEthAmount;
        uint256 tokenAmounts = virtualTokenLp - newTokenAmount;
        return tokenAmounts;
    }

    function ethAmount(uint256 _tokenAmount) internal view returns(uint256) {
        uint256 newTokenAmount = virtualTokenLp + _tokenAmount;
        uint256 newEthAmount = k / newTokenAmount;
        uint256 ethAmounts = virtualEthLp - newEthAmount;
        return ethAmounts;
    }

    function currentTokenPrice() public view returns(uint256) {
        return (virtualEthLp) * (10 ** 15) / virtualTokenLp;
    }

    function ethOrTokenAmount(uint256 _amount, uint8 _id) external view returns(uint256) {
        uint256 mainFee = FactoryContract(factoryContract).mainFee();
        if (_id == 0){
            uint256 ethAmounts = ethAmount(_amount);
            ethAmounts = (ethAmounts * (100 - mainFee)) / 100;
            return ethAmounts;
        } else {
            _amount = (_amount * (100 - mainFee)) / 100;
            return tokenAmount(_amount);
        }
    }

    function finalize() internal {
        lpCreated = true;
        Ownable(token).renounceOwnership();
        IERC20(token).safeApprove(router, realTokenLp);
        uint256 tokenBalance = IERC20(token).balanceOf(address(this));
        if (tokenBalance < realTokenLp) {
            realTokenLp = tokenBalance;
        } else {
            uint256 remainTokens = tokenBalance - realTokenLp;
            IERC20(token).transfer(address(0xdead), remainTokens);
        }
        IUniswapV2Router01(router).addLiquidityETH{value: address(this).balance * 8 / 10}(
            token,
            realTokenLp,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            address(0xdead),
            block.timestamp + 400
        );
        address feeAddress = FactoryContract(factoryContract).devWallet();
        payable(feeAddress).transfer(address(this).balance);
    }

    function emergencyWithdraw() external {
        address feeAddress = FactoryContract(factoryContract).devWallet();
        require(feeAddress == msg.sender && IERC20(token).balanceOf(address(this)) == total);
        payable(feeAddress).transfer(address(this).balance);
    }

    function getTrending() external view returns (uint256){
        uint256 rate;
        if(!lpCreated)
        {
            rate = virtualEthLp / (block.timestamp - startTimestamp);
        }else{
            rate = 0;
        }
        return rate;
    }

    function getRisingPercent() external view returns (uint256) {
        uint256 currentTime = block.timestamp;
        uint256 time24HoursAgo = currentTime - 24 hours;
        uint256 len = tokenPriceDatas.length;

        TokenPriceData memory firstPriceData24HoursAgo;
        bool found = false;

        // Find the first data with time smaller than 24 hours ago
        for (uint256 i = len; i > 0; i--) {
            TokenPriceData memory data = tokenPriceDatas[i - 1];
            if (data.time < time24HoursAgo) {
                firstPriceData24HoursAgo = data;
                found = true;
                break;
            }
        }

        uint256 lastClose = tokenPriceDatas[len - 1].close;

        uint256 risingPercent;

        if (found) {
            // Check for underflow before calculation
            if (lastClose >= firstPriceData24HoursAgo.close) {
                risingPercent = (lastClose - firstPriceData24HoursAgo.close) * 10000 / firstPriceData24HoursAgo.close;
            } else {
                risingPercent = 0; // Return 0 if there's an underflow
            }
        } else {
            uint256 firstClose = tokenPriceDatas[0].close;
            // Check for underflow before calculation
            if (lastClose >= firstClose) {
                risingPercent = (lastClose - firstClose) * 10000 / firstClose;
            } else {
                risingPercent = 0; // Return 0 if there's an underflow
            }
        }

        return risingPercent;
    }

    function getFunBasicInfo() external view returns(uint256 [10] memory, string [7] memory, address [4] memory, address [] memory, bool){
        uint256 [10] memory tokenDatas = [total, startTimestamp, maxBuy, tokenStartPrice, virtualTokenLp, virtualEthLp, totalRefAmounts, uint256(refCount), currentTokenPrice(), volume];
        string [7] memory strings = [name, symbol, website, twitter, telegram, discord, info];
        address [4] memory addresses = [address(this), token, owner(), router];
        return ((tokenDatas), (strings), (addresses), (refAddresses), lpCreated);
    }

    function getAllPrices() external view returns(TokenPriceData [] memory){
        return((tokenPriceDatas));
    }
}

// File: SmartContracts/Factory.sol


pragma solidity ^0.8.9;

contract Factory is Ownable {
    using SafeERC20 for IERC20;
    address[] allSafuHubs;
    address payable public devWallet;
    uint256 public feeAmount;
    address public dexRouter;
    uint8 public mainFee = 1;  // default trade fee is 1%
    mapping(address => address[]) safuHubLists;
    uint256 public virtualTokenLp = 1073 * (10 ** 27);  // 1073 * (10 ** 9) amounts
    uint256 public virtualEthLp;
    uint256 public bondingLimit;
    uint256 public lockPeriod = 856800;
    uint8 public maxBuyPercentage = 1;
    mapping(address => address[]) public userContributors;
    mapping(address => bool) public safuHubAddresses;

    constructor(
        address _feeAddress,
        uint256 _feeAmount,
        address _dexRouter,
        uint256 _virtualEthLp,
        uint256 _bondingLimit
    ) {
        devWallet = payable(_feeAddress);
        feeAmount = _feeAmount;
        dexRouter = _dexRouter;
        virtualEthLp = _virtualEthLp;
        bondingLimit = _bondingLimit;
    }
    
    receive() external payable {
    }
    
    function createSafuHub(
        string [] memory tokenDatas //name, symbol, description, website, twitter, telegram, discord
    ) external payable returns (address) {        
        require(msg.value >= feeAmount, "Insufficient Amount");
        devWallet.transfer(feeAmount);

        Coin coin = new Coin(address(this), msg.sender, tokenDatas, 1000000000000, 18, lockPeriod);
        address coinAddr = address(coin);

        uint256 tokenBalance = IERC20(coin).balanceOf(address(this));

        uint256 newEthLp = virtualEthLp + (msg.value - feeAmount);
        uint256 newTokenLp = virtualEthLp * virtualTokenLp / newEthLp;
        uint256 tokenAmount = virtualTokenLp - newTokenLp;

        uint256 k = virtualEthLp * virtualTokenLp;

        require(maxBuyPercentage <= 100, "Invalid Max Buy Amount");
        require(tokenAmount <= tokenBalance * maxBuyPercentage / 100);
        PumpData memory pumpData = PumpData(
            tokenAmount,
            msg.value - feeAmount,
            virtualEthLp,
            virtualTokenLp,
            k
        );

        AddressData memory addressData = AddressData(
            coinAddr,
            address(this),
            dexRouter
        );

        SafuHub safuHub = new SafuHub(msg.sender, tokenDatas, maxBuyPercentage, addressData, pumpData);
        address safuHubAddr = address(safuHub);
        payable(safuHubAddr).transfer(msg.value - feeAmount);

        IERC20(coin).transfer(address(safuHub), tokenBalance - tokenAmount);
        IERC20(coin).transfer(msg.sender, tokenAmount);
        Ownable(coin).transferOwnership(safuHubAddr);
        allSafuHubs.push(safuHubAddr);
        safuHubLists[msg.sender].push(safuHubAddr);
        safuHubAddresses[safuHubAddr] = true;
        return safuHubAddr;
    }

    function updateDatas(uint256 _newFee, uint8 _mainFee, uint256 _bondingLimit, address payable _newDev) external onlyOwner{
        feeAmount = _newFee;
        mainFee = _mainFee;
        bondingLimit = _bondingLimit;
        devWallet = _newDev;
    }

    function updateLockPeriod(uint256 _newLockPeriod) external onlyOwner{
        lockPeriod = _newLockPeriod;
    }

    function updateMaxBuyPercentage(uint8 _newMaxBuyPercentage) external onlyOwner{
        require(_newMaxBuyPercentage <= 100, "Invalid Max Buy Amount");
        maxBuyPercentage = _newMaxBuyPercentage;
    }

    function updateContributors(address _user, address _safuhub) external {
        require(safuHubAddresses[msg.sender] == true);
        userContributors[_user].push(_safuhub);
    }

    function getAllAddresses() external view returns(address [] memory){
        return((allSafuHubs));
    }

    function getUserContributorAddresses(address _user) external view returns(address [] memory){
        return((userContributors[_user]));
    }

    function funUserLists(address _user) external view returns (address [] memory){
        return (safuHubLists[_user]);
    }

    function updateVirtualLiquidity(uint256 _ethLp, uint256 _tokenLp) external onlyOwner {
        virtualEthLp = _ethLp;
        virtualTokenLp = _tokenLp;
    }
}