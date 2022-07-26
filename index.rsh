'reach 0.1';

const [ isHand, ROCK, PAPER, SCISSORS ] = makeEnum(3);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

const winner = (handA, handB) => (handA + (4 - handB)) % 3;

assert(winner(ROCK, PAPER) == B_WINS);
assert(winner(PAPER, ROCK) == A_WINS);
assert(winner(ROCK, ROCK) == DRAW);

forall(UInt, handA =>
    forall(UInt, handB =>
        assert(isOutcome(winner(handA, handB)))));

forall(UInt, (hand) => 
    assert(winner(hand, hand) == DRAW));

// Participant Interact interface
const Player = {
    ...hasRandom,
    getHand: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
    informTimeout: Fun([], Null),
}

//  App initialization: definition of Players
export const main = Reach.App(() => {

    const Alice = Participant('Alice', {
        // Alice interact object here
        ...Player,
        wager: UInt,
        deadline: UInt, // time delta (blocks/rounds)
    });

    const Bob = Participant('Bob', {
        // Bob interact object here
        ...Player,
        acceptWager: Fun([UInt], Null),
    });

    const informTimeout = () => {
        each([Alice, Bob], () => {
            interact.informTimeout()
        })
    }

    init();

    // Write the logic
    Alice.only(() => {
        const wager = declassify(interact.wager)
        const deadline = declassify(interact.deadline)
     })

    Alice.publish(wager, deadline)
         .pay(wager);
    commit();
     
    Bob.only(() => {
        interact.acceptWager(wager);
    })

    Bob.pay(wager)
    .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout))

    var outcome = DRAW;
    invariant(balance() == 2 * wager && isOutcome(outcome));

    while( outcome == DRAW ) {
        commit()

        Alice.only(() => {
            const _handAlice = interact.getHand()
            const [ _commitAlice, _saltAlice ] = makeCommitment(interact, _handAlice);
            const commitAlice = declassify(_commitAlice);
        })

        Alice.publish(commitAlice)
        .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout))

        commit()

        unknowable(Bob, Alice(_handAlice, _saltAlice));

        Bob.only(() => {
        const handBob = declassify(interact.getHand());
        })

        Bob.publish(handBob)
        .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout))

        commit()

        Alice.only(() => {
            const saltAlice = declassify(_saltAlice);
            const handAlice = declassify(_handAlice);
        })
    
        Alice.publish(saltAlice, handAlice)
        .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout))
    
        checkCommitment(commitAlice, saltAlice, handAlice);

        // Outcome of the game
        outcome = winner(handAlice, handBob);

        continue
    }

    assert( outcome == A_WINS || outcome == B_WINS );

    transfer(2 * wager).to(outcome == A_WINS ? Alice : Bob);

    commit()

    each([Alice, Bob], () => {
        interact.seeOutcome(outcome);
    })

})
