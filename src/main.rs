use std::{io, fmt, cmp};
use itertools::iproduct;
use std::time::Instant;
use rand::Rng;
use std::collections::{HashSet, VecDeque};
use std::f64::consts::SQRT_2;

macro_rules! parse_input {
    ($x:expr, $t:ident) => ($x.trim().parse::<$t>().unwrap())
}

const NUM_PLAY_D: usize = 2;
const NUM_OPP_D: usize = 2;
const MAX_DRONES: usize = NUM_PLAY_D + NUM_OPP_D;
const MAX_SCANS: usize = 10;
const MAX_CREATURES: usize = 22;
const GRID_MAX_X: usize = 100;
const GRID_MAX_Y: usize = 100;

const UGLY_EAT_RANGE: i32 = 300;  //from cg ?
const DRONE_HIT_RANGE: i32 = 200; // from cg ?

const D_MONSTER_EMER: f64 = 500.0;
const MONSTER_SPEED_ANGRY: i32 = 540;
const MONSTER_MAX_Y: i32 = 2500;

const D_MAX_DRONE: i32 = 600;
const D_GRID_MAX_DRONE: i32 = D_MAX_DRONE/GRID_MAX_X as i32;

const LIGHT_STD: i32 =  800;
const LIGHT_UPDATED: i32 =  2000;
const GRID_LIGHT_STD: i32 = LIGHT_STD / GRID_MAX_X as i32;

const BOARD_MAX_X: usize = 10000;
const BOARD_MAX_Y: usize = 10000;



#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GridPoint { 
    x:i32,
    y:i32,
}
impl fmt::Display for GridPoint {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	fmt.write_str(&format!("gr({}, {})",self.x,self.y))?;
        Ok(())
    }
}

impl GridPoint {
    fn dist(p1: &GridPoint, p2: &GridPoint) -> f64 {
	let dx = f64::from(p1.x - p2.x);
	let dy = f64::from(p1.y - p2.y);
	(dx * dx + dy * dy).sqrt()
    }
    fn de_gridify(&self) -> Point {
	Point {x:self.x * GRID_MAX_X as i32, y:self.y * GRID_MAX_Y as i32}
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Point { 
    x:i32,
    y:i32,
}

impl fmt::Display for Point {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	fmt.write_str(&format!("({}, {})",self.x,self.y))?;
        Ok(())
    }
}

impl Point {
    fn dist(p1: &Point, p2: &Point) -> f64 {
	let dx = f64::from(p1.x - p2.x);
	let dy = f64::from(p1.y - p2.y);
	(dx * dx + dy * dy).sqrt()
    }
    fn gridify(&self) -> GridPoint {
	GridPoint {x:(self.x as f32/GRID_MAX_X as f32).round() as i32, y:(self.y as f32/GRID_MAX_Y as f32).round() as i32}
    }

     fn in_range(&self, v: Point, range: i32) -> bool {
        (v.x - self.x) * (v.x - self.x) + (v.y - self.y) * (v.y - self.y) <= range * range
    }
    fn in_grid(&self, g: GridSlice) -> bool {
	if g.is_unique {
	    self == &g.p_min
	}
	else {
	    self.x >= g.p_min.x && self.x < g.p_max.x && self.y >= g.p_min.y && self.y < g.p_max.y
	}
    }

    fn div(&self, d_f:f64) -> Point{
	Point {x:(self.x as f64/d_f ) as i32, y:(self.y as f64 /d_f) as i32}
    }

    fn add(a: Point, b: Point) -> Point {
	Point { x: a.x + b.x, y: a.y + b.y }
    }
}


#[derive(Debug, PartialEq, Clone, Copy)]
enum MapLocation {
    T, // tout en haut
    H, // en haut
    M, // millieu
    B, // bas
    Mo, // monster
}

impl MapLocation {
    fn to_min_max_pts(ml: MapLocation) -> (Point, Point) {
	match ml {
	    MapLocation::T => (Point {x:0,y:0}, Point {x:BOARD_MAX_X as i32,y:2500}),
	    MapLocation::H => (Point {x:0,y:2500}, Point {x:BOARD_MAX_X as i32,y:5000}),
	    MapLocation::M => (Point {x:0,y:5000}, Point {x:BOARD_MAX_X as i32,y:7500}),
	    MapLocation::B => (Point {x:0,y:7500}, Point {x:BOARD_MAX_X as i32,y:10000}),
	    MapLocation::Mo => (Point {x:0,y:2500}, Point {x:BOARD_MAX_X as i32,y:10000}),
	}
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RadarDir {
    TL, // : la créature est en haut à gauche du drone.
    TR, // : la créature est en haut à droite du drone.
    BR, // : la créature est en bas à droite du drone.
    BL, // : la créature est en bas à gauche du drone.
}

#[derive(Debug, Copy, Clone)]
struct FishDetail {
    color: i32,
    fish_type: i32,
}
impl FishDetail {
    fn get_zone(&self) -> MapLocation {
	match self.fish_type {
	    0 => MapLocation::H,
	    1 => MapLocation::M,
	    2 => MapLocation::B,
	    _ => MapLocation::Mo,
	}
    }
}

#[derive(Debug, Clone, Copy)]
struct Fish {
    fish_id: i32,
    pos: Point,
    speed: Point,
    detail: FishDetail,
}

#[derive(Debug, Clone)]
struct RadarBlip {
    fish_id: i32,
    fish_detail: FishDetail,
    dir: RadarDir,
}

#[derive(Debug, Clone, Copy)]
struct Scan {
    f_id:i32,
    proba: f64,
}

#[derive(Debug, Clone)]
struct Drone {
    drone_id: i32,
    pos: Point,
    emergency: bool,
    battery: i32,
    scans: Vec<Scan>,
    radars: Option<Vec<RadarBlip>>,
    prev_action: Option<Action>,
    go_up: bool,
}

impl Drone {
    fn where_i_am(&self) -> MapLocation {
	if self.pos.y < 2500 {
           return MapLocation::T;
	}
	else if  self.pos.y < 5000 {
            return MapLocation::H;
	}
	else if self.pos.y < 7500 {
            return MapLocation::M;
	}
	else {
            return MapLocation::B;
	}
    }
}

#[derive(Debug, Clone)]
struct Score {
    num_by_type: [i32;3], //3 types
    num_by_color:[i32;4],
    my_score: i32,
    opp_score: i32,
}

impl Score {

    fn get_my_max_possible_sc(&self) -> i32{
	let mut max_sc = self.my_score
	    + (4-self.num_by_type[0])*2
	    + (4-self.num_by_type[1])*4
	    + (4-self.num_by_type[2])*6;

	for &n_c in &self.num_by_color {
	    if n_c == 0 {
		max_sc += 6;
	    }
	}

	for &n_t in &self.num_by_type {
	    if n_t == 0 {
		max_sc += 8;
	    }
	}

	max_sc
    }

    fn get_best_type(&self) -> Option<i32> {
	if self.num_by_type[2] > 0 {
	    return Some(2);
	}
	if self.num_by_type[1] > 0 {
	    return Some(1);
	}
	if self.num_by_type[0] > 0 {
	    return Some(0);
	}

	None
    }
    
    fn from_init_state(my_s: i32, opp_s: i32, my_scan: &Vec<Scan>, my_d: &Vec<Drone>, hash_fishes: &[Option<FishDetail>;MAX_CREATURES]) -> Score {


	let mut h_se = HashSet::new();
	
	let mut ro_num_by_type= [0;3]; 
	let mut ro_num_by_color = [0;4];

	//total number
	let d = &my_d[0]; //take first radars (there are same)
	for r in d.radars.as_ref().unwrap() {
	    if r.fish_detail.fish_type != - 1 {
	    	h_se.insert(r.fish_id);
	    }
	}

	for sc in my_scan {
	    h_se.remove(&sc.f_id);
	}

	for d in my_d {
	    for sc in &d.scans {
		h_se.remove(&sc.f_id);
	    }
	}

	for &fid in  h_se.iter() {
	    let fd = hash_fishes[fid as usize].unwrap();
	    ro_num_by_color[fd.color as usize] += 1;
	    ro_num_by_type[fd.fish_type as usize] += 1;
	}

	Score {my_score:my_s, opp_score:opp_s, num_by_color:ro_num_by_color, num_by_type:ro_num_by_type}

	
    }
}

#[derive(Debug, Clone)]
struct Board {

    score_mg: Score,
    
    my_scans: Vec<Scan>,
    opp_scans: Vec<Scan>,

    my_drones: Vec<Drone>,
    opp_drones: Vec<Drone>,

    visible_fishes: Vec<Fish>,

    grid_sliced: [Option<GridSlice>; MAX_CREATURES],

    predition_level: i32, //0 for the initial level
    game_turn: i32,

    hash_fishes: [Option<FishDetail>;MAX_CREATURES],
    //fish_details: &HashMap<i32, FishDetail>,
}

impl Board {
    fn merge_board(cur_b:&Board, prev_b:&Board) -> Board {
	let mut m_prev = prev_b.clone();
	let mut out_b = cur_b.clone();
	
	for (f_id,(fd_t, sg_t)) in m_prev.hash_fishes.iter().zip(m_prev.grid_sliced.iter_mut()).enumerate() {
		if let (Some(fd),Some(sg)) = (fd_t, sg_t) {

		    let accel_to_add;
		    
		    if fd.fish_type == -1 {
			accel_to_add = 540.0; //we don't know if panicked or not
		    } else {
			accel_to_add = 400.0; //idem
		    }
		    // add the computed acceleration
		    let mut new_sg = *sg;
		    new_sg.p_min = Point::add(new_sg.p_min, Point {x:-(accel_to_add/SQRT_2) as i32, y:-(accel_to_add/SQRT_2) as i32});
		    new_sg.p_max = Point::add(new_sg.p_max, Point {x:(accel_to_add/SQRT_2) as i32, y:(accel_to_add/SQRT_2) as i32});
		    new_sg.is_unique = false;
		    
		    new_sg.p_min.x = i32::max(0, new_sg.p_min.x);
		    new_sg.p_min.y = i32::max(0, new_sg.p_min.y);
		    new_sg.p_max.x = i32::max(0, new_sg.p_max.x);
		    new_sg.p_max.y = i32::max(0, new_sg.p_max.y);

		    new_sg.p_min.x = i32::min(10000, new_sg.p_min.x);
		    new_sg.p_min.y = i32::min(10000, new_sg.p_min.y);
		    new_sg.p_max.x = i32::min(10000, new_sg.p_max.x);
		    new_sg.p_max.y = i32::min(10000, new_sg.p_max.y);
			
		    //clamp to area

		    let gs_f = GridSlice::from_map_loc(fd.get_zone());
		    let inter = new_sg.intersec(gs_f);
		    *sg = inter;
		}
	}

	//now update visible fishes
	eprintln!("up merge");
	//update position of drone
	m_prev.my_drones = out_b.my_drones.clone();
	m_prev.opp_drones = out_b.opp_drones.clone();
	
	m_prev.update_entities_first_pred();

	//merge visible fish
	for f in &m_prev.visible_fishes.clone() {
	   if !out_b.visible_fishes.iter().any(|fi| fi.fish_id == f.fish_id) {
	       out_b.visible_fishes.push(*f);
	   }
	}
	
	for f in m_prev.visible_fishes.iter() {
	    // update of removed fishes is done in update_entities...
	    m_prev.grid_sliced[f.fish_id as usize] = Some(GridSlice::from_unique_pt(f.pos));
	}

	// if more precision in the previous table, keep it
	for (prev_grid_t, out_grid_t) in m_prev.grid_sliced.iter().zip(out_b.grid_sliced.iter_mut()) {
	    if let (Some(prev_grid), Some(out_grid)) = (prev_grid_t, out_grid_t) {
		if prev_grid.num_elems() < out_grid.num_elems() {
		    *out_grid = *prev_grid;
		}
	    }
	    	    
	}
	out_b
    }
    
    fn from_input_board(ib: &InputlBoard) -> Board {
	let mut tab_creat :[Option<GridSlice>; MAX_CREATURES] = [None; MAX_CREATURES];
	
	for d in ib.my_drones.iter().chain(ib.opp_drones.iter()) {
	    let gs = GridSlice::from_unique_pt(d.pos);
	    tab_creat[d.drone_id as usize] = Some(gs); 
	}

	//update based on radar
	for d in ib.my_drones.iter() {
	    //radar
	    for r in d.radars.as_ref().unwrap().iter() {
		let gs_r = GridSlice::from_radar(d.pos, r.dir);
		let gs_f = GridSlice::from_map_loc(r.fish_detail.get_zone());
		let inter = gs_r.intersec(gs_f);

		if let Some(gs_e) = &mut tab_creat[r.fish_id as usize] {
		    *gs_e = gs_e.intersec(inter);
		}
		else {
		  tab_creat[r.fish_id as usize] = Some(inter);  
		}		
	    }
	}

	for f in ib.visible_fishes.iter() {
	    eprintln!("visi fish {}", f.fish_id);
	    tab_creat[f.fish_id as usize] = Some(GridSlice::from_unique_pt(f.pos));
	}

	for (idx,i) in tab_creat.iter().enumerate() {
	    if let Some(it) = i {
		//eprintln!("fid {} - {}", idx, it);
	    }
	}

	// Score creation
	let sc = Score::from_init_state(ib.my_score, ib.opp_score, &ib.my_scans, &ib.my_drones, &ib.hash_fishes);
	
	Board {score_mg:sc, my_scans:ib.my_scans.clone(), opp_scans: ib.opp_scans.clone(), my_drones:ib.my_drones.clone(), opp_drones:ib.opp_drones.clone(), visible_fishes:ib.visible_fishes.clone(), grid_sliced:tab_creat, predition_level:0, hash_fishes:ib.hash_fishes, game_turn:ib.game_turn}
    }


    fn snap_to_fish_zone(fish: &mut Fish) {
	let (p_max, p_min) = MapLocation::to_min_max_pts(fish.detail.get_zone());
	if fish.pos.y > BOARD_MAX_Y  as i32 - 1 {
            fish.pos.y = BOARD_MAX_Y  as i32 - 1;
	} else if fish.pos.y > p_max.y {
            fish.pos.y = p_max.y;
	} else if fish.pos.y < p_min.y {
            fish.pos.y = p_min.y;
	}
    }
    
    fn snap_to_ugly_zone(ugly: &mut Fish) {
	if ugly.pos.y > BOARD_MAX_Y  as i32- 1 {
            ugly.pos.y = BOARD_MAX_Y as i32- 1;
	} else if ugly.pos.y <MONSTER_MAX_Y {
            ugly.pos.y = MONSTER_MAX_Y;
	}
    }

    fn snap_to_drone_zone(drone: &mut Drone) {
	if drone.pos.y > BOARD_MAX_Y as i32- 1 {
            drone.pos.y = BOARD_MAX_Y as i32 - 1;
	} else if drone.pos.y < 0 {
            drone.pos.y = 0;
	}
	
	if drone.pos.x < 0 {
            drone.pos.x = 0;
	} else if drone.pos.x >= BOARD_MAX_X as i32 {
            drone.pos.x = BOARD_MAX_X as i32 - 1;
	}
    }

    /// first pred, all vectors are GT
    fn update_entities_first_pred(&mut self) {
	// !!!  we consider no collision since we only allow direction without collision
	let mut to_rem = Vec::new();
	for e in self.visible_fishes.iter_mut() {
	    e.pos = Point::add(e.pos,e.speed);
	    if e.detail.fish_type == -1 {
		Board::snap_to_ugly_zone(e);

		//update speed
		let (closest_dis, closest_dr) = self.my_drones.iter()
		    .chain(self.opp_drones.iter())
		    .map(|d| (Point::dist(&d.pos, &e.pos), d))
		    .min_by(|x0,x1| x0.0.partial_cmp(&x1.0).unwrap())
		    .unwrap();

		let  d_light = LIGHT_UPDATED; //TODO change if light on
	
		if (closest_dis as i32) <= d_light {
		    //go to the direction of the drone	    
		    let v_abs = Point {x:closest_dr.pos.x - e.pos.x, y: closest_dr.pos.y - e.pos.y};
		    let (dx_n, dy_n) = ((MONSTER_SPEED_ANGRY as f64/closest_dis), ( MONSTER_SPEED_ANGRY as f64/closest_dis));
		    let p_new = Point {x:((v_abs.x as f64)*dx_n) as i32,y:((v_abs.y as f64)*dy_n) as i32};
		    e.speed = p_new;
		} 
		
	    } else {
		Board::snap_to_fish_zone(e);
		if e.pos.x < 0 || e.pos.x >= BOARD_MAX_X as i32 {
		    to_rem.push(e.fish_id);
		    //remove fish from the table
		    self.grid_sliced[e.fish_id as usize] = None;
		}
	    }
	}
	self.visible_fishes.retain(|f| !to_rem.contains(&f.fish_id)); //remove fish that disapears
    }
    
    fn next_board(&self, ac_play: &[Action;NUM_PLAY_D], ac_opp: &[Action;NUM_OPP_D]) -> Board {
	//focus on monster for now
	
	let mut out_b = self.clone();
	out_b.predition_level += 1;

	for (idx,d) in out_b.my_drones.iter_mut().enumerate() {
	    match ac_play[idx] {
		Action::MOVE(p, l) => {d.pos = p;
				       d.prev_action = Some(ac_play[idx]);},
		Action::WAIT(l) => (eprintln!("HEUUU wait...")),
	    }
	}
	
	for d in out_b.my_drones.iter().chain(out_b.opp_drones.iter()) {
	    let gs = GridSlice::from_unique_pt(d.pos);
	    out_b.grid_sliced[d.drone_id as usize] = Some(gs); 
	}
	

	if out_b.predition_level == 1 {
	    //add all fish with know position to visible fish
	    out_b.update_entities_first_pred();
	    for f in out_b.visible_fishes.iter() {
		//eprintln!("visi fish {}", f.fish_id);
		// update of removed fishes is done in update_entities...
		out_b.grid_sliced[f.fish_id as usize] = Some(GridSlice::from_unique_pt(f.pos));
	    }
	    
	    out_b.visible_fishes.clear(); //no visible fishes for the other prediction
	} else {
	    // we are in > 1 step, lets improvise...
	    for (f_id,(fd_t, sg_t)) in out_b.hash_fishes.iter().zip(out_b.grid_sliced.iter_mut()).enumerate() {
		if let (Some(fd),Some(sg)) = (fd_t, sg_t) {
		    let mut rng = rand::thread_rng();
		    let n_rand = rng.gen_range(0..10);

		    let accel_to_add;
		    
		    if fd.fish_type == -1 {
			let mons_accel;
			if out_b.predition_level < 8 {
			    // 0 at the begining
			    mons_accel = 0;
			} else {
			    if n_rand >= 8 {
				//sometime, big acceleration
				mons_accel = 540;
			    } else {
				mons_accel = 270;
			    }
			}
			accel_to_add = mons_accel as f64;
		    } else {
			let fish_accel;
			if n_rand >= 8 {
			    //sometime, big acceleration
			    fish_accel = 400;
			} else {
			    fish_accel = 200;
			}
			accel_to_add = fish_accel as f64;
		    }
		    // add the computed acceleration
		    let mut new_sg = *sg;
		    new_sg.p_min = Point::add(new_sg.p_min, Point {x:-(accel_to_add/SQRT_2) as i32, y:-(accel_to_add/SQRT_2) as i32});
		    new_sg.p_max = Point::add(new_sg.p_max, Point {x:(accel_to_add/SQRT_2) as i32, y:(accel_to_add/SQRT_2) as i32});
		    new_sg.is_unique = false;
		    
		    new_sg.p_min.x = i32::max(0, new_sg.p_min.x);
		    new_sg.p_min.y = i32::max(0, new_sg.p_min.y);
		    new_sg.p_max.x = i32::max(0, new_sg.p_max.x);
		    new_sg.p_max.y = i32::max(0, new_sg.p_max.y);

		    new_sg.p_min.x = i32::min(10000, new_sg.p_min.x);
		    new_sg.p_min.y = i32::min(10000, new_sg.p_min.y);
		    new_sg.p_max.x = i32::min(10000, new_sg.p_max.x);
		    new_sg.p_max.y = i32::min(10000, new_sg.p_max.y);
			
		    //clamp to area

		    let gs_f = GridSlice::from_map_loc(fd.get_zone());
		    let inter = new_sg.intersec(gs_f);

		    *sg = inter;

		    // now check if there is new possible scan with this new location and a drone
		    for d in out_b.my_drones.iter_mut().chain(out_b.opp_drones.iter_mut()) {
			if Point::dist(&d.pos, &sg.center()) <= LIGHT_UPDATED as f64 {
			    //ok lets add a scan is not inside
			    if !d.scans.iter().any(|s| s.f_id == f_id as i32) {
				//ok not present add
				d.scans.push(Scan {f_id:f_id as i32, proba:0.8});
			    }
			}
		    }
		}
	    }
	}
	
	
	out_b	
    }

    fn eval_position(&self) -> f64 {
	let mut to_add = 0.0;
	let mut dist_fish = [None;MAX_CREATURES]; //dist from drone 0 and 1

	for (idx,gs_t) in self.grid_sliced.iter().enumerate() {
	    if let Some(gs) = gs_t {
		dist_fish[idx] = Some([Point::dist(&self.my_drones[0].pos, &gs.center()), Point::dist(&self.my_drones[1].pos, &gs.center())]);
	    }
	}

	for (f_id,(fd_t, sg_t)) in self.hash_fishes.iter().zip(self.grid_sliced.iter()).enumerate() {
	    if let (Some(fd),Some(sg)) = (fd_t, sg_t) {
		if fd.fish_type == -1{
		    if dist_fish[f_id].unwrap()[0] < 600.0 || dist_fish[f_id].unwrap()[1] < 600.0 {
			to_add -= 1.0/sg.num_elems() as f64;
		   }
		}
	    }
	}
	

	let mut dist_max = 0.0;

	let mut dist_max_monster = 0.0;
	let mut num_monster = 0;
	
	let mut cur_score = self.score_mg.clone();

	let mut res_dist = [[None;NUM_PLAY_D];NUM_PLAY_D];
	
	for (id_d_up,d_up) in self.my_drones.iter().enumerate() {
	    let type_obj_try = cur_score.get_best_type();
	    if let Some(type_obj) = type_obj_try {	    
		cur_score.num_by_type[type_obj as usize] -= 1;
		//eprintln!("to take {} {}", type_obj, id_d_up);
		for (id_d,d) in self.my_drones.iter().enumerate() {
		    let mut min_v = f64::MAX;
		    for (f_id,(fd_t, sg_t)) in self.hash_fishes.iter().zip(self.grid_sliced.iter()).enumerate() {
			if let (Some(fd),Some(sg)) = (fd_t, sg_t) {
			    
			    if fd.fish_type == -1 {
				dist_max_monster += dist_fish[f_id].unwrap()[id_d]/sg.num_elems() as f64;
				num_monster += 1;
			    }
			    
			    if fd.fish_type == -1 || f_id == d.drone_id as usize{ continue;}
			    if fd.fish_type != type_obj {continue;}
			    if !self.my_drones[0].scans.iter().chain(self.my_drones[1].scans.iter()).any(|s| s.f_id == f_id as i32) && !self.my_scans.iter().any(|s| s.f_id == f_id as i32){
				//fid is the target
				if dist_fish[f_id].unwrap()[id_d] < min_v {
				    min_v = dist_fish[f_id].unwrap()[id_d];
				}
			    }
			}
		    }
		    res_dist[id_d_up as usize][id_d as usize] = Some(min_v/10000.0);
		}
		//dist_max += min_v/10000.0;
	    }
	}
	
	if self.score_mg.get_my_max_possible_sc() > 50 && !self.my_drones[0].scans.is_empty() && !self.my_drones[1].scans.is_empty()  {
	    res_dist[0][0] = None;
	    res_dist[0][1] = None;
	    
	}
	if self.score_mg.get_my_max_possible_sc() > 50 && !self.my_drones[0].scans.is_empty() {
	    res_dist[1][0] = None;
	    
	    if let  (Some(rd1), Some(rd2)) = (res_dist[0][0], res_dist[0][1]) {
		if rd1 < rd2 {
		    res_dist[0][0] = Some(rd2);
		    res_dist[0][1] = Some(rd1);
		}
	    }
	}

	if self.score_mg.get_my_max_possible_sc() > 50 && !self.my_drones[1].scans.is_empty() {
	    res_dist[1][1] = None;
	    if let  (Some(rd1), Some(rd2)) = (res_dist[0][0], res_dist[0][1]) {
		if rd1 >= rd2 {
		    res_dist[0][0] = Some(rd2);
		    res_dist[0][1] = Some(rd1);
		}
	    }

	}

	if let (Some(rd1), Some(rd2)) = (res_dist[0][0], res_dist[0][1]) {
	    if rd1 < rd2 {
		dist_max += rd1;
		if let Some(rd2_p) =  res_dist[1][1] {
		    dist_max += rd2_p;
		} else {
		    //go up for the drone 2
		    dist_max += self.my_drones[1].pos.y as f64;
		}
	    } else {
		dist_max += rd2;
		if let Some(rd1_p) =  res_dist[1][0] {
		    dist_max += rd1_p;
		} else {
		    //go up for the drone 1
		    dist_max += self.my_drones[0].pos.y as f64;
		}
	    }
	} else {
	    dist_max += self.my_drones[0].pos.y as f64;
	    dist_max += self.my_drones[1].pos.y as f64;
	}

	dist_max_monster /= num_monster as f64;
	dist_max_monster /= 10000.0;

	Point::dist(&self.my_drones[0].pos, &self.my_drones[1].pos) / 100000.0 	// drones should be distant
	    - 2.0*dist_max/2.0
	    + 2.0*to_add
    }

    fn get_possible_actions_play(&self) -> [[Option<Action>;8]; NUM_PLAY_D] {
	let mut ret_val = [[None;8]; NUM_PLAY_D];

	for (idxd, d) in self.my_drones.iter().enumerate() {
	    let pa = self.get_successor(d.pos.gridify());
	    for (idxa, &a) in pa.iter().enumerate() {
		if let Some(a_o) = a {
		    ret_val[idxd][idxa] = Some(Action::MOVE(a_o.de_gridify(), false));
		}
		
	    }
	}
	ret_val
    }

    fn monster_collision(&self, d_start: Point, d_speed: Point ) -> bool {
	for f in self.visible_fishes.iter() {
	    if f.detail.fish_type == -1 {
		if f.pos.in_range(d_start, DRONE_HIT_RANGE + UGLY_EAT_RANGE) {
		    return true;
		}
		// Change referential
		let x = f.pos.x;
		let y = f.pos.y;
		let ux = d_start.x;
		let uy = d_start.y;
		
		let x2 = x - ux;
		let y2 = y - uy;
		let r2 = UGLY_EAT_RANGE + DRONE_HIT_RANGE;
		let vx2 = f.speed.x - d_speed.x;
		let vy2 = f.speed.y - d_speed.y;

		let a = f64::from(vx2 * vx2 + vy2 * vy2);

		if a <= 0.0 {
		    continue;
		}

		let b = 2.0 * (x2 * vx2 + y2 * vy2) as f64;
		let c = f64::from(x2 * x2 + y2 * y2 - r2 * r2);
		let delta = f64::from(b * b - 4.0 * a * c);

		if delta < 0.0 {
		    continue
		}

		let t = (-b - delta.sqrt()) / (2.0 * a);
		
		if t <= 0.0 || t > 1.0 {
		    continue
		}

		return true;
            }
	}
	return false;
    }

    
    fn get_successor(&self, p:GridPoint) -> [Option<GridPoint>;8] {
	let mut ret_tab = [None;8];
	let mut idx = 0; // bug enumerae

	for (dx_a,dy_a) in iproduct!([-1,0,1], [-1,0,1]) {
	    if dx_a == 0 && dy_a == 0 {
		continue;
	    }
	    let dist = GridPoint::dist(&GridPoint {x:0,y:0} ,&GridPoint {x:dx_a,y:dy_a});
	    let (dx_n, dy_n) = ((D_GRID_MAX_DRONE as f64/dist), (D_GRID_MAX_DRONE as f64/dist));
	    let speed_drone =  GridPoint { x:((dx_a as f64)*dx_n) as i32,y:((dy_a as f64)*dy_n) as i32};
	    let mut p_new = GridPoint {x:p.x + ((dx_a as f64)*dx_n) as i32,y:p.y + ((dy_a as f64)*dy_n) as i32};
	    
	    if p_new.x < 0 || p_new.x >= GRID_MAX_X as i32|| p_new.y < 0 || p_new.y >= GRID_MAX_X as i32{
		p_new.x = i32::max(0, p_new.x);
		p_new.y = i32::max(0, p_new.y);
		
		p_new.x = i32::min(9999, p_new.x);
		p_new.y = i32::min(9999, p_new.y);
			
	    }

	    if self.monster_collision(p.de_gridify(), speed_drone.de_gridify() ) {
		continue;
	    }
	    ret_tab[idx] = Some(p_new);
	    idx +=1;
	}

	ret_tab
    }

    /// search best position
    fn bfs_search(&self) -> Option<[Action; NUM_PLAY_D]> {
	let mut queue: VecDeque<(Board, Option<[Action; NUM_PLAY_D]>, i32)> = VecDeque::new();
	queue.push_back((self.clone(), None, 0));
	let mut max_position = f64::MIN;
	let mut max_board = None;
	let mut deep;
	let mut num_simu = 0;
	
	let start = Instant::now();
	
	while !queue.is_empty() {
	    let (cur_board, first_action, cur_deep) = &queue.pop_front().unwrap();
	    deep = *cur_deep;
	    
	    let duration = start.elapsed();
	    if deep > 1 || duration.as_millis() > 40 {
		eprintln!("BREAK deep {} simu {} ms {}", deep, num_simu, duration.as_millis());
		break;
	    }

	    let acts = cur_board.get_possible_actions_play(); 
	    for (ac1_try,ac2_try) in iproduct!(acts[0],acts[1]) { //cartesian product of all actions		    
		if let (Some(ac1), Some(ac2)) = (ac1_try, ac2_try) {
		    let next_board = cur_board.next_board(&[ac1,ac2],&[ac1,ac2]);
		    if next_board.predition_level > 1 {
			continue;
		    }
		    
		    num_simu += 1;
		    
		    let to_put;
		    if deep == 0 {
			to_put = Some([ac1,ac2]);
		    }
		    else {
			to_put = first_action.clone();
		    }
		    queue.push_back((next_board.clone(), to_put, cur_deep + 1));

		    let next_pos_val = next_board.eval_position();
		    
		    if next_pos_val > max_position {
			max_position = next_pos_val;
			max_board = to_put;
		    }
		}
	    }
	}
	max_board
    }
}

#[derive(Debug)]
struct InputlBoard {
    my_score: i32,
    opp_score: i32,
    hash_fishes: [Option<FishDetail>;MAX_CREATURES],

    my_scans: Vec<Scan>,
    opp_scans: Vec<Scan>,

    my_drones: Vec<Drone>,
    opp_drones: Vec<Drone>,

    visible_fishes: Vec<Fish>,

    game_turn: i32,
    
  }


#[derive(Debug, Copy, Clone)]
enum Action { 
    MOVE(Point, bool), 
    WAIT(bool),
}


impl fmt::Display for Action {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
  	match self {
	    Action::MOVE(p, l) => fmt.write_str(&format!("MOVE {} {} {}",p.x,p.y,*l as i32))?,
	    Action::WAIT(l) => fmt.write_str(&format!("WAIT {}", *l as i32))?,
	}
        Ok(())
    }
}


#[derive(Debug, Clone, Copy)]
/// points are note in the gridified space !!
struct GridSlice {
    p_min: Point,
    p_max: Point,
    is_unique: bool,

}

impl fmt::Display for GridSlice {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	if self.is_unique {
	    assert_eq!(self.p_min, self.p_max);
	    assert_eq!(self.p_min, self.center());
	    assert_eq!(self.num_elems(), 1);
		
	    fmt.write_str(&format!("p: {} ** UNI **",self.p_min))?;
	} else {
	    fmt.write_str(&format!("p_min: {}, p_max: {} (center: {}) (sz {})",self.p_min,self.p_max, self.center(), self.num_elems()))?;
	}
        Ok(())
    }
}

impl GridSlice {
    /// num elems for the gridified slice
    fn num_elems(&self) -> i32 {
	if !self.is_unique {
	    let min_y = self.p_min.gridify().y as usize;
	    let min_x = self.p_min.gridify().x as usize;
	    let max_y = self.p_max.gridify().y as usize;
	    let max_x = self.p_max.gridify().x as usize;
	    ((max_x - min_x)*(max_y - min_y)) as i32
	} else {
	    1
	}		
    }

    fn from_tuple(pts: (Point, Point)) -> GridSlice {
	let (p_min, p_max) = pts;
	GridSlice {p_min, p_max, is_unique:false}
	
    }

    fn intersec(&self, gs:GridSlice) -> GridSlice {
	let min_y1 = self.p_min.y as usize;
	let min_x1 = self.p_min.x as usize;
	let max_y1 = self.p_max.y as usize;
	let max_x1 = self.p_max.x as usize;

	let min_y2 = gs.p_min.y as usize;
	let min_x2 = gs.p_min.x as usize;
	let max_y2 = gs.p_max.y as usize;
	let max_x2 = gs.p_max.x as usize;

	let min_x_n = cmp::max(min_x1, min_x2);
	let max_x_n = cmp::min(max_x1, max_x2);
	let min_y_n = cmp::max(min_y1, min_y2);
	let max_y_n = cmp::min(max_y1, max_y2);

	GridSlice {p_min: Point {x:min_x_n as i32, y:min_y_n as i32}, p_max: Point {x:max_x_n as i32, y:max_y_n as i32}, is_unique:false}
	
    }

    fn from_radar(d_pos: Point, r_dir: RadarDir) -> GridSlice {
	match r_dir {
	    RadarDir::BL => GridSlice {p_min: Point {x:0,y:d_pos.y}, p_max: Point {x:d_pos.x, y:BOARD_MAX_Y as i32}, is_unique:false},
	    RadarDir::BR => GridSlice {p_min: d_pos , p_max: Point {x:BOARD_MAX_X as i32,y:BOARD_MAX_Y as i32}, is_unique:false},
	    RadarDir::TL => GridSlice {p_min: Point {x:0,y:0}, p_max: d_pos, is_unique:false},
	    RadarDir::TR => GridSlice {p_min: Point {x:d_pos.x, y:0}, p_max: Point {x:BOARD_MAX_X as i32,y:d_pos.y}, is_unique:false},
	}
    }

    fn from_map_loc(ml: MapLocation) -> GridSlice {
	GridSlice::from_tuple(MapLocation::to_min_max_pts(ml))
    }
    fn from_unique_pt(pt: Point) -> GridSlice {
	GridSlice {p_max:pt, p_min:pt, is_unique:true }
    }

    fn center(&self) -> Point {
	if !self.is_unique {
	    Point {x:self.p_min.x + (self.p_max.x - self.p_min.x)/2, y:self.p_min.y + (self.p_max.y - self.p_min.y)/2}
	} else {
	    assert_eq!(self.p_min, self.p_max);
	    self.p_min
	}
    }
}



/**
 * Score points by scanning valuable fish faster than your opponent.
 **/
fn main() {
    let mut v_board = Vec::new();
    let mut prev_action: [Option<Action>; MAX_DRONES] = [None; MAX_DRONES];
    
    //let mut hash_fish = HashMap::new();
    let mut hash_fish = [None; MAX_CREATURES];
    
    let mut input_line = String::new();
    io::stdin().read_line(&mut input_line).unwrap();
    let creature_count = parse_input!(input_line, i32);
    for _ in 0..creature_count as usize {
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let inputs = input_line.split(" ").collect::<Vec<_>>();
        let creature_id = parse_input!(inputs[0], i32);
        let color = parse_input!(inputs[1], i32);
        let fish_type = parse_input!(inputs[2], i32);
	assert!(creature_id <= 21);
	hash_fish[creature_id as usize] = Some(FishDetail {color, fish_type});

    }

    // game loop
    let mut cur_step = 0;

    //let left_right = HashMap::new();
    let mut initial_left = None;
    loop {
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let my_score = parse_input!(input_line, i32);
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let foe_score = parse_input!(input_line, i32);
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
	let mut my_scans = Vec::new();
        let my_scan_count = parse_input!(input_line, i32);
        for _ in 0..my_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let creature_id = parse_input!(input_line, i32);
	    my_scans.push(Scan {f_id:creature_id, proba:1.0});
        }
	let mut opp_scans = Vec::new();
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let foe_scan_count = parse_input!(input_line, i32);
        for _ in 0..foe_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let creature_id = parse_input!(input_line, i32);
	    opp_scans.push(Scan {f_id:creature_id, proba:1.0});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();

	let mut my_drones= Vec::new();
        let my_drone_count = parse_input!(input_line, i32);
        for idx_d in 0..my_drone_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let drone_x = parse_input!(inputs[1], i32);
            let drone_y = parse_input!(inputs[2], i32);
            let emergency = parse_input!(inputs[3], i32);
            let battery = parse_input!(inputs[4], i32);
	    if cur_step == 0 {
		if drone_x < 5000 {
		    initial_left = Some(drone_id);
		}
	    }
	    my_drones.push(Drone {drone_id:drone_id, pos:Point{x:drone_x,y:drone_y}, emergency:emergency==1,battery:battery,scans:Vec::new(),radars:Some(Vec::new()), prev_action:prev_action[drone_id as usize],go_up:false});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
	let mut opp_drones= Vec::new();
        let foe_drone_count = parse_input!(input_line, i32);
        for _ in 0..foe_drone_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let drone_x = parse_input!(inputs[1], i32);
            let drone_y = parse_input!(inputs[2], i32);
            let emergency = parse_input!(inputs[3], i32);
            let battery = parse_input!(inputs[4], i32);
	    opp_drones.push(Drone {drone_id:drone_id, pos:Point{x:drone_x,y:drone_y}, emergency:emergency==1,battery:battery,scans:Vec::new(),radars:None, prev_action:None, go_up:false});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let drone_scan_count = parse_input!(input_line, i32);
        for _ in 0..drone_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let creature_id = parse_input!(inputs[1], i32);
	    opp_drones.iter_mut()
		.chain(my_drones.iter_mut())
		.find(|e| e.drone_id == drone_id)
		.unwrap()
		.scans.push(Scan {f_id:creature_id, proba:1.0});
	    
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let visible_creature_count = parse_input!(input_line, i32);
	let mut visible_fishes = Vec::new();
	
        for _ in 0..visible_creature_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let creature_id = parse_input!(inputs[0], i32);
            let creature_x = parse_input!(inputs[1], i32);
            let creature_y = parse_input!(inputs[2], i32);
            let creature_vx = parse_input!(inputs[3], i32);
            let creature_vy = parse_input!(inputs[4], i32);
	    visible_fishes.push(Fish {fish_id:creature_id,pos: Point{x:creature_x, y:creature_y},speed: Point{x:creature_vx, y:creature_vy}, detail: hash_fish[creature_id as usize].unwrap()});
        }

        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let radar_blip_count = parse_input!(input_line, i32);
        for _ in 0..radar_blip_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let creature_id = parse_input!(inputs[1], i32);
            let radar = inputs[2].trim(); //.to_string();

	    let radar_dir = match radar {
		"BL" => Ok(RadarDir::BL),
		"TL" => Ok(RadarDir::TL),
		"TR" => Ok(RadarDir::TR),
		"BR" => Ok(RadarDir::BR),
		_ => Err("Bad radar direction"),
	    };

	    	    
	    my_drones.iter_mut()
		.find(|e| e.drone_id == drone_id)
		.unwrap()
		.radars.as_mut().unwrap().push(RadarBlip {fish_id:creature_id, dir:radar_dir.unwrap(),fish_detail: hash_fish[creature_id as usize].unwrap()});
        }
	
	let input_board = InputlBoard {hash_fishes:hash_fish, my_scans, opp_scans, my_drones, opp_drones, my_score:my_score, opp_score:foe_score, visible_fishes, game_turn:cur_step};
	let board_init = Board::from_input_board(&input_board);

	let board;
	if !v_board.is_empty() {
	    board = Board::merge_board(&board_init, &v_board.last().unwrap());
	}
	else {
	    board = board_init;
	}
	v_board.push(board.clone());
	
	let start = Instant::now();


	let found_acts = board.bfs_search();

	if let Some(acts) = found_acts {
	    
	    for (id_d,ac) in acts.iter().enumerate() {
		let loc = board.my_drones[id_d].where_i_am();
		let mut light = false;
		if  board.my_drones[id_d].battery >= 5 && loc != MapLocation::T && (cur_step as usize + id_d) % 2 == 0 {
                    light = true;
		}
		if let Action::MOVE(p, _) = ac {
		    println!("{}", Action::MOVE(*p, light));
		} else {
		     println!("{} HEUUUU, ", ac);
		}
	    }
	} else {
	    let ac = Action::WAIT(false);
	    println!("{} mmmh, ", ac);
	    println!("{} mmmh, ", ac);
	}

	let duration = start.elapsed();
	eprintln!("TIME {:?}", duration);
	cur_step += 1;
    }
}
