'reach 0.1';

const [ isFingers, ZERO, ONE, TWO, THREE, FOUR, FIVE] = makeEnum(6);
const [ isGuess, GZERO, GONE, GTWO, GTHREE, GFOUR, GFIVE, GSIX, GSEVEN, GEIGHT, GNINE, GTEN ] = makeEnum(11);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

const winner = (fingersA, fingersB, guessA, guessB) => { 
  if ( guessA == guessB ) 
   {
    const myOutcome = DRAW; 
    return myOutcome;
} else {
  if ( ((fingersA + fingersB) == guessA ) ) {
    const myOutcome = A_WINS;
    return myOutcome;
  } 
    else {
      if (  ((fingersA + fingersB) == guessB)) {
        const myOutcome = B_WINS;
        return myOutcome;
    } 
      else {
        const myOutcome = DRAW;
        return myOutcome;
      }
    }
  }
};

assert(winner(ZERO,TWO,GZERO,GTWO)== B_WINS);
assert(winner(TWO,ZERO,GTWO,GZERO)== A_WINS);
assert(winner(ZERO,ONE,GZERO,GTWO)== DRAW);
assert(winner(ONE,ONE,GONE,GONE)== DRAW);


forall(UInt, fingersA =>
  forall(UInt, fingersB =>
    forall(UInt, guessA =>
      forall(UInt, guessB =>
    assert(isOutcome(winner(fingersA, fingersB, guessA, guessB)))))));

forall(UInt, (fingerA) =>
  forall(UInt, (fingerB) =>       
    forall(UInt, (guess) =>
      assert(winner(fingerA, fingerB, guess, guess) == DRAW))));    

const Player =
      { ...hasRandom,
        getFingers: Fun([], UInt),
        getGuess: Fun([UInt], UInt),
        seeWinning: Fun([UInt], Null),
        seeOutcome: Fun([UInt], Null) ,
        informTimeout: Fun([], Null)
       };
const Alice =
        { ...Player,
          wager: UInt, 
          ...hasConsoleLogger
        };
const Bob =
        { ...Player,
          acceptWager: Fun([UInt], Null),
          ...hasConsoleLogger           
        };
const DEADLINE = 30; 

export const main =
  Reach.App(
    {},
    [Participant('Alice', Alice), Participant('Bob', Bob)],
    (A, B) => {
        const informTimeout = () => {
          each([A, B], () => {
            interact.informTimeout(); }); };
      A.only(() => {
        const wager = declassify(interact.wager); });
      A.publish(wager)
        .pay(wager);
      commit();   

      B.only(() => {
        interact.acceptWager(wager); });
      B.pay(wager)
        .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));

      var outcome = DRAW;      
      invariant(balance() == 2 * wager && isOutcome(outcome) );
      while ( outcome == DRAW ) {
        commit();
        A.only(() => {    
          const _fingersA = interact.getFingers();
          const _guessA = interact.getGuess(_fingersA);  
          interact.log(_fingersA);  
                      
          const [_commitA, _saltA] = makeCommitment(interact, _fingersA);
          const commitA = declassify(_commitA);        
          const [_guessCommitA, _guessSaltA] = makeCommitment(interact, _guessA);
          const guessCommitA = declassify(_guessCommitA);   
      });
     
        A.publish(commitA)
          .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        commit();    

        A.publish(guessCommitA)
          .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
          ;
        commit();
        unknowable(B, A(_fingersA, _saltA));
        unknowable(B, A(_guessA, _guessSaltA));

        B.only(() => {

          const _fingersB = interact.getFingers();
          const _guessB = interact.getGuess(_fingersB);
          const fingersB = declassify(_fingersB); 
          const guessB = declassify(_guessB);  

          });

        B.publish(fingersB)
          .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));
        commit();
        B.publish(guessB)
          .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));
          ;
        
        commit();
        A.only(() => {
          const [saltA, fingersA] = declassify([_saltA, _fingersA]); 
          const [guessSaltA, guessA] = declassify([_guessSaltA, _guessA]); 

        });
        A.publish(saltA, fingersA)
          .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        checkCommitment(commitA, saltA, fingersA);
        commit();

        A.publish(guessSaltA, guessA)
        .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        checkCommitment(guessCommitA, guessSaltA, guessA);

        commit();
      
        A.only(() => {        
          const winningNumber = fingersA + fingersB;
          interact.seeWinning(winningNumber);
        });
     
        A.publish(winningNumber)
        .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));

        outcome = winner(fingersA, fingersB, guessA, guessB);
        continue; 
       
      }

      assert(outcome == A_WINS || outcome == B_WINS);
      transfer(2 * wager).to(outcome == A_WINS ? A : B);
      commit();
 
      each([A, B], () => {
        interact.seeOutcome(outcome); 
    })
      exit(); 
});
