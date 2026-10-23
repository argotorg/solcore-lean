import {
    origin, gasprice, coinbase, timestamp, number, prevrandao, gaslimit,
    chainid, basefee, blobbasefee, blockhash, blobhash,
    extcodesize, extcodehash, extcodecopy, callcode, delegatecall,
    create, create2, selfdestruct, mstore, return_
} from std.opcodes;

contract AmbientWrappers {
    function main() {
        mstore(0, origin());
        mstore(32, gasprice());
        mstore(64, coinbase());
        mstore(96, timestamp());
        mstore(128, number());
        mstore(160, prevrandao());
        mstore(192, gaslimit());
        mstore(224, chainid());
        mstore(256, basefee());
        mstore(288, blobbasefee());
        mstore(320, blockhash(44));
        mstore(352, blobhash(0));
        return_(0, 384);
    }
}

contract InspectionWrappers {
    function main() {
        mstore(0, extcodesize(3276));
        mstore(32, extcodehash(3276));
        extcodecopy(3276, 64, 0, 3);
        return_(0, 96);
    }
}

contract CallModeWrappers {
    function main() {
        mstore(0, callcode(50000, 3276, 7, 0, 0, 0, 0));
        mstore(32, delegatecall(50000, 3276, 0, 0, 0, 0));
        return_(0, 64);
    }
}

contract CreationWrappers {
    function main() {
        mstore(0, create(0, 0, 0));
        mstore(32, create2(0, 0, 0, 77));
        return_(0, 64);
    }
}

contract DestructionWrapper {
    function main() {
        selfdestruct(3567);
        mstore(0, 99);
        return_(0, 32);
    }
}
