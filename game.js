const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');
let W = canvas.width = innerWidth;
let H = canvas.height = innerHeight;

const TILE = 32;                
const COLS = Math.floor(W / TILE) >= 15 ? Math.floor(W / TILE) : 21;
const ROWS = Math.floor(H / TILE) >= 11 ? Math.floor(H / TILE) : 15;
const GRID_COLS = (COLS % 2 === 1) ? COLS : COLS - 1;
const GRID_ROWS = (ROWS % 2 === 1) ? ROWS : ROWS - 1;

const gridW = GRID_COLS;
const gridH = GRID_ROWS;

let maze = []; 
let player = { x:1, y:1, speed:140, w:16, h:20 };
let cam = { x:0, y:0 };

const state = {
  paused: false,
  score: 0,
  truth: 0,
  doubt: 0,
  visited: new Set(),
  ending: null,
  exitLocked: true,        
  keyFragmentsFaced: 0    
};

const keys = {};
window.addEventListener('keydown', e=>{ keys[e.key]=true; if(e.key===' '){ tryInteract(); } });
window.addEventListener('keyup', e=>{ keys[e.key]=false; });

function randInt(a,b){ return Math.floor(Math.random()*(b-a+1))+a; }
function shuffle(a){ for(let i=a.length-1;i>0;i--){ const j=Math.floor(Math.random()*(i+1)); [a[i],a[j]]=[a[j],a[i]]; } }
function clamp(v,a,b){ return Math.max(a,Math.min(b,v)); }


function makeEmptyGrid(){ maze = new Array(gridH).fill(0).map(()=>new Array(gridW).fill(1)); }

function generateMaze(){
  makeEmptyGrid();
  const startX=1,startY=1;
  maze[startY][startX]=0;
  const stack=[[startX,startY]];
  const dirs=[[2,0],[-2,0],[0,2],[0,-2]];

  while(stack.length){
    const [cx,cy]=stack[stack.length-1];
    const order=dirs.slice(); shuffle(order);
    let carved=false;
    for(const [dx,dy] of order){
      const nx=cx+dx, ny=cy+dy;
      if(nx>0 && ny>0 && nx<gridW-1 && ny<gridH-1 && maze[ny][nx]===1){
        maze[ny][nx]=0;
        maze[cy+dy/2][cx+dx/2]=0;
        stack.push([nx,ny]);
        carved=true;
        break;
      }
    }
    if(!carved) stack.pop();
  }


  const q=[[startX,startY,0]]; const seen={}; seen[`${startX},${startY}`]=0;
  let far=[startX,startY,0];
  while(q.length){
    const [x,y,d]=q.shift();
    if(d>far[2]) far=[x,y,d];
    for(const [dx,dy] of [[1,0],[-1,0],[0,1],[0,-1]]){
      const nx=x+dx, ny=y+dy;
      if(nx>=0 && ny>=0 && nx<gridW && ny<gridH && maze[ny][nx]===0 && seen[`${nx},${ny}`]===undefined){
        seen[`${nx},${ny}`]=d+1; q.push([nx,ny,d+1]);
      }
    }
  }

  maze[far[1]][far[0]]=2;


  const candidates=Object.keys(seen).filter(k=>seen[k]>=Math.max(6,Math.floor(Math.max(gridW,gridH)/3)));
  shuffle(candidates);
  const nodeCount=Math.min(5,Math.max(2,Math.floor(candidates.length/6)));
  for(let i=0;i<nodeCount;i++){
    const [c,r]=candidates[i].split(',').map(Number);
    maze[r][c]=3;
  }
}


function findPath(sx,sy,tx,ty){
  const key0=`${sx},${sy}`;
  const q=[[sx,sy]]; const prev={}; prev[key0]=null;
  while(q.length){
    const [x,y]=q.shift();
    if(x===tx && y===ty){
      const path=[];
      let cur=`${x},${y}`;
      while(cur){ const [cx,cy]=cur.split(',').map(Number); path.push([cx,cy]); cur=prev[cur]; }
      path.reverse(); return path;
    }
    for(const [dx,dy] of [[1,0],[-1,0],[0,1],[0,-1]]){
      const nx=x+dx, ny=y+dy;
      if(nx>=0 && ny>=0 && nx<gridW && ny<gridH && maze[ny][nx]!==1){
        const key=`${nx},${ny}`;
        if(prev[key]===undefined){ prev[key]=`${x},${y}`; q.push([nx,ny]); }
      }
    }
  }
  return null;
}


function mutateMazeSafely(){
  let exit=null;
  for(let r=0;r<gridH;r++) for(let c=0;c<gridW;c++) if(maze[r][c]===2) exit=[c,r];
  if(!exit) return;
  const px=Math.floor(player.x), py=Math.floor(player.y);
  const path=findPath(px,py,exit[0],exit[1]);
  const protectedSet=new Set();
  if(path) path.forEach(p=>protectedSet.add(`${p[0]},${p[1]}`));
  protectedSet.add(`${px},${py}`);
  protectedSet.add(`${exit[0]},${exit[1]}`);

  // Deceptive openings
  for(let i=0;i<10;i++){
    const cx=randInt(1,gridW-2), cy=randInt(1,gridH-2);
    const key=`${cx},${cy}`;
    if(!protectedSet.has(key) && maze[cy][cx]===1){
      maze[cy][cx]=0;
      if(Math.random()<0.6){
        const dirs=[[1,0],[-1,0],[0,1],[0,-1]]; shuffle(dirs);
        const [dx,dy]=dirs[0];
        const nx=cx+dx, ny=cy+dy;
        if(nx>0 && ny>0 && nx<gridW-1 && ny<gridH-1 && !protectedSet.has(`${nx},${ny}`)) maze[ny][nx]=0;
      }
    }
  }

  // Corrupt some branches
  const candidates=[];
  for(let r=1;r<gridH-1;r++) for(let c=1;c<gridW-1;c++){
    const k=`${c},${r}`;
    if(!protectedSet.has(k) && maze[r][c]===0) candidates.push([c,r]);
  }
  shuffle(candidates);
  let attempts=0;
  for(const [c,r] of candidates.slice(0,20)){
    if(attempts>12) break;
    maze[r][c]=1;
    if(!findPath(px,py,exit[0],exit[1])) maze[r][c]=0;
    else attempts++;
  }
}


const MEMORY_FRAGMENTS=[
  { id:'left_home', text:"You left home before saying goodbye...", effectGood:(x,y)=>{
      state.truth++; openPathNear(x,y); showHint('You acknowledged the past.');
      keyFragmentCheck();
    }, effectBad:(x,y)=>{ state.doubt++; mutateMazeSafely(); showHint('You pushed it away.'); } },
  { id:'lost_friend', text:"A photo falls open — a laugh frozen...", effectGood:(x,y)=>{
      state.truth++; openCriticalPaths(); showHint('You kept the promise.');
      keyFragmentCheck();
    }, effectBad:(x,y)=>{ state.doubt++; mutateMazeSafely(); showHint('You refused to remember.'); } },
  { id:'cheated_exam', text:"You once lied to get ahead...", effectGood:(x,y)=>{
      state.truth++; openPathNear(x,y); showHint('Facing it thins the fog.');
      keyFragmentCheck();
    }, effectBad:(x,y)=>{ state.doubt++; mutateMazeSafely(); showHint('Denial breeds labyrinthine doubt.'); } },
  { id:'silent_parent', text:"You wanted to tell them but the words never formed.", effectGood:(x,y)=>{
      state.truth++; openCriticalPaths(); showHint('A corridor straightens under your feet.');
      keyFragmentCheck();
    }, effectBad:(x,y)=>{ state.doubt++; mutateMazeSafely(); showHint('You close your mouth.'); } },
  { id:'stranger_watch', text:"A stranger watched and smiled...", effectGood:(x,y)=>{
      state.truth++; revealExit(); showHint('You looked. The maze answers.');
      keyFragmentCheck();
    }, effectBad:(x,y)=>{ state.doubt++; mutateMazeSafely(); showHint('The stranger laughs; paths rearrange.'); } },
  { id:'forgot_pet', text:"Your childhood pet waited...", effectGood:(x,y)=>{
      state.truth++; openPathNear(x,y); showHint('You remember warmth.');
      keyFragmentCheck();
    }, effectBad:(x,y)=>{ state.doubt++; mutateMazeSafely(); showHint('You ignore it.'); } }
];

// Check key fragments to unlock exit after 3 “faced”
function keyFragmentCheck(){
  state.keyFragmentsFaced++;
  if(state.keyFragmentsFaced>=3){
    revealExit();
    showHint('A hidden exit opens...');
  }
}

function mapFragmentAt(cx,cy){ const i=Math.abs(cx*9+cy*7)%MEMORY_FRAGMENTS.length; return MEMORY_FRAGMENTS[i]; }


function openDialog(fragmentKey,cx,cy){
  state.paused=true;
  const frag=fragmentKey;
  const overlay=document.createElement('div'); overlay.className='dialog-overlay';
  const box=document.createElement('div'); box.className='dialog-box';
  const h=document.createElement('h2'); h.textContent='Memory Fragment'; box.appendChild(h);
  const p=document.createElement('p'); p.textContent=frag.text; box.appendChild(p);
  const actions=document.createElement('div'); actions.className='dialog-actions';
  const btnGood=document.createElement('button'); btnGood.textContent='Face it';
  btnGood.onclick=()=>{ frag.effectGood(cx,cy); closeDialog(overlay,`${cx},${cy}`); if(audioEnv) adjustAmbience(); };
  const btnBad=document.createElement('button'); btnBad.textContent='Ignore'; btnBad.className='secondary';
  btnBad.onclick=()=>{ frag.effectBad(cx,cy); closeDialog(overlay,`${cx},${cy}`); if(audioEnv) adjustAmbience(); };
  actions.appendChild(btnBad); actions.appendChild(btnGood); box.appendChild(actions); overlay.appendChild(box); document.body.appendChild(overlay);
}

function closeDialog(overlay,key){ state.paused=false; if(overlay && overlay.parentNode) overlay.parentNode.removeChild(overlay); if(key) state.visited.add(key); }


function openPathNear(cx,cy){ for(let r=cy-2;r<=cy+2;r++) for(let c=cx-2;c<=cx+2;c++) if(maze[r] && maze[r][c]===1) maze[r][c]=0; }
function openCriticalPaths(){ for(let i=0;i<40;i++){ const r=randInt(1,gridH-2), c=randInt(1,gridW-2); if(maze[r][c]===1) maze[r][c]=0; } }

// Exit unlock
function revealExit(){ state.exitLocked=false; }


function currentCell(){ return [Math.floor(player.x),Math.floor(player.y)]; }
function tryInteract(){
  const [cx,cy]=currentCell();
  if(maze[cy] && maze[cy][cx]===3){
    const key=`${cx},${cy}`;
    if(state.visited.has(key)){ showHint('Already resolved.'); return; }
    const frag=mapFragmentAt(cx,cy); openDialog(frag,cx,cy);
  } else showHint('Nothing here.');
}


function showHint(msg){
  const b=document.createElement('div'); b.className='hint-bubble'; b.textContent=msg; document.body.appendChild(b);
  b.animate([{opacity:0},{opacity:1},{opacity:1},{opacity:0}],{duration:2600}).onfinish=()=>b.remove();
}


function atExit(){ const [cx,cy]=currentCell(); return maze[cy] && maze[cy][cx]===2 && !state.exitLocked; }
function checkEnd(){
  if(state.ending) return;
  if(state.truth>=5){ state.ending='true'; endOverlay('True Ending — The mind opens'); }
  else if(state.doubt>=6){ state.ending='dark'; endOverlay('Dark Ending — The walls win'); }
  else if(atExit()){ state.ending='escape'; endOverlay('Escape — You leave, but the root remains'); }
}

function endOverlay(title){
  state.paused=true;
  const overlay=document.createElement('div'); overlay.className='dialog-overlay';
  const box=document.createElement('div'); box.className='dialog-box';
  const h=document.createElement('h2'); h.textContent=title; box.appendChild(h);
  const p=document.createElement('p');
  if(title.startsWith('True')) p.textContent=`You faced what you hid. Light pours through cracks.\nTruth: ${state.truth}`;
  else if(title.startsWith('Dark')) p.textContent=`You let doubt steer you. The maze settles.\nDoubt: ${state.doubt}`;
  else p.textContent=`You found an exit. The maze remains a lesson.\nTruth: ${state.truth} Doubt: ${state.doubt}`;
  box.appendChild(p);
  const actions=document.createElement('div'); actions.className='dialog-actions';
  const btnReplay=document.createElement('button'); btnReplay.textContent='Play Again'; btnReplay.onclick=()=>{ document.body.removeChild(overlay); resetGame(); };
  const btnReload=document.createElement('button'); btnReload.textContent='Reload Page'; btnReload.onclick=()=>location.reload(); btnReload.className='secondary';
  actions.appendChild(btnReload); actions.appendChild(btnReplay); box.appendChild(actions); overlay.appendChild(box); document.body.appendChild(overlay);
}


function render(){
  ctx.clearRect(0,0,W,H);
  ctx.fillStyle='#041018'; ctx.fillRect(0,0,W,H);
  const px=player.x*TILE, py=player.y*TILE;
  cam.x=px-W/2; cam.y=py-H/2; cam.x=clamp(cam.x,0,gridW*TILE-W); cam.y=clamp(cam.y,0,gridH*TILE-H);

  for(let r=0;r<gridH;r++) for(let c=0;c<gridW;c++){
    const cell=maze[r][c], sx=c*TILE-cam.x, sy=r*TILE-cam.y;
    if(cell===1){ ctx.fillStyle='#072026'; ctx.fillRect(sx,sy,TILE,TILE); }
    else if(cell===2 && !state.exitLocked){ ctx.fillStyle='#ffd166'; ctx.fillRect(sx+6,sy+6,TILE-12,TILE-12); }
    else if(cell===3){ const key=`${c},${r}`; ctx.fillStyle=state.visited.has(key)?'#7be6c3':'#5eead4'; ctx.fillRect(sx+8,sy+8,TILE-16,TILE-16); }
    else{ ctx.fillStyle='#031019'; ctx.fillRect(sx,sy,TILE,TILE); ctx.fillStyle='rgba(255,255,255,0.01)'; ctx.fillRect(sx+2,sy+2,4,4); }
  }

  ctx.save(); ctx.translate(player.x*TILE-cam.x,player.y*TILE-cam.y); ctx.fillStyle='#bbf3ff'; ctx.fillRect(-player.w/2,-player.h/2,player.w,player.h); ctx.restore();
  ctx.fillStyle='#dbeafe'; ctx.font='14px system-ui'; ctx.fillText(`Truth: ${state.truth}  Doubt: ${state.doubt}`,12,20);
}


let last=performance.now();
function update(dt){
  if(state.paused) return;
  let dx=0, dy=0;
  if(keys.ArrowLeft||keys.a) dx=-1;
  if(keys.ArrowRight||keys.d) dx=1;
  if(keys.ArrowUp||keys.w) dy=-1;
  if(keys.ArrowDown||keys.s) dy=1;
  if(dx!==0 && dy!==0){ dx*=0.707; dy*=0.707; }
  const nx=player.x+dx*player.speed*dt/TILE;
  const ny=player.y+dy*player.speed*dt/TILE;
  if(canMoveTo(nx,player.y)) player.x=nx;
  if(canMoveTo(player.x,ny)) player.y=ny;
  const [cx,cy]=currentCell();
  if(maze[cy] && maze[cy][cx]===3 && !state.visited.has(`${cx},${cy}`)) if(audioEnv) playWhisperStrike();
  checkEnd();
}

function canMoveTo(px,py){ const gx=Math.floor(px), gy=Math.floor(py); return gx>=0 && gy>=0 && gx<gridW && gy<gridH && maze[gy][gx]!==1; }

function loop(now){ const dt=Math.min(0.05,(now-last)/1000); last=now; update(dt); render(); requestAnimationFrame(loop); }


let audioCtx, audioEnv;
let ambienceGain, whisperGain;
let ambienceOsc, whisperOsc;

function initAudio(){
    try {
        audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        ambienceGain = audioCtx.createGain(); ambienceGain.gain.value=0.05; ambienceGain.connect(audioCtx.destination);
        whisperGain = audioCtx.createGain(); whisperGain.gain.value=0.0; whisperGain.connect(audioCtx.destination);

        ambienceOsc = audioCtx.createOscillator();
        ambienceOsc.type='sine'; ambienceOsc.frequency.value=50;
        ambienceOsc.connect(ambienceGain); ambienceOsc.start();

        whisperOsc = audioCtx.createOscillator();
        whisperOsc.type='triangle'; whisperOsc.frequency.value=200;
        whisperOsc.connect(whisperGain); whisperOsc.start();

        audioEnv = true;
    } catch(e){
        console.log('Audio not supported or blocked.', e);
        audioEnv = false;
    }
}

function adjustAmbience(){
    if(!audioEnv) return;
    const t = state.truth, d = state.doubt;
    const gain = clamp(0.05 + 0.02*d - 0.01*t, 0.02, 0.2);
    ambienceGain.gain.linearRampToValueAtTime(gain, audioCtx.currentTime+0.5);
}

function playWhisperStrike(){
    if(!audioEnv) return;
    whisperGain.gain.cancelScheduledValues(audioCtx.currentTime);
    whisperGain.gain.setValueAtTime(0.2, audioCtx.currentTime);
    whisperGain.gain.linearRampToValueAtTime(0.0, audioCtx.currentTime + 0.6);
}

// Start audio on first user gesture
let audioInitialized=false;
function initAudioOnGesture(){
    if(audioInitialized) return;
    initAudio();
    adjustAmbience();
    audioInitialized=true;
    console.log('Audio started!');
}
window.addEventListener('keydown', initAudioOnGesture, {once:true});
window.addEventListener('mousedown', initAudioOnGesture, {once:true});


function resetGame(){
    state.truth=0; state.doubt=0; state.visited=new Set(); state.ending=null;
    state.exitLocked=true; state.keyFragmentsFaced=0;
    player.x=1; player.y=1;
    generateMaze(); 
    if(audioEnv) adjustAmbience();
}

window.addEventListener('resize', ()=>{ W=canvas.width=innerWidth; H=canvas.height=innerHeight; });


generateMaze();
requestAnimationFrame(loop);

const settingsBtn = document.getElementById('settingsBtn');
const settingsOverlay = document.getElementById('settingsOverlay');
const closeSettings = document.getElementById('closeSettings');
const volumeRange = document.getElementById('volumeRange');

settingsBtn.addEventListener('click', ()=> settingsOverlay.style.display='flex');
closeSettings.addEventListener('click', ()=> settingsOverlay.style.display='none');


volumeRange.addEventListener('input', ()=>{
    if(!audioEnv) return;
    const vol = parseInt(volumeRange.value)/100; 
    if(ambienceGain) ambienceGain.gain.setTargetAtTime(vol*0.05, audioCtx.currentTime, 0.01);
    if(whisperGain) whisperGain.gain.setTargetAtTime(vol*0.1, audioCtx.currentTime, 0.01);
});

const startOverlay = document.getElementById('startOverlay');
const beginBtn = document.getElementById('beginBtn');

beginBtn.addEventListener('click', () => {
    startOverlay.style.display = 'none'; 
    resetGame(); 
});
