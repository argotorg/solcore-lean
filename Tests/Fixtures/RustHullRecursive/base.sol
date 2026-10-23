enum Chain {
    End(word),
    Link(word, Chain)
}

function relay(value: Chain) returns (Chain) {
    assembly { mstore(96, 1) }
    return value;
}

function inspect(value: Chain) returns (word) {
    assembly { mstore(96, 2) }
    match (value) {
        case Chain.End(payload) { return payload; }
        case Chain.Link(head, _) { return head; }
    }
}

contract Recursive {
    function main() {
        let input: word;
        assembly { input := calldataload(0) }
        let result: word = inspect(relay(Chain.End(input)));
        assembly {
            mstore(0, result)
            return(0, 32)
        }
    }
}
