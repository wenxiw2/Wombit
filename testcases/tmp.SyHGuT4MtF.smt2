(push 1)
(set-info :source | fuzzsmt 0.3 |)
(set-logic  QF_ABV)
(set-info :status unknown)
(declare-fun v4303 () (_ BitVec 6))
(declare-fun v4304 () (_ BitVec 5))
(declare-fun v4305 () (_ BitVec 3))
(declare-fun v4306 () (_ BitVec 4))
(declare-fun a4307 () (Array (_ BitVec 10) (_ BitVec 11)))
(assert
(let ((e4308 (_ bv35452 16)))
(let ((e4309 (bvor ((_ sign_extend 12) v4306) e4308)))
(let ((e4310 (ite (bvuge ((_ zero_extend 3) v4305) v4303)(_ bv1 1) (_ bv0 1))))
(let ((e4311 (bvudiv ((_ sign_extend 3) e4310) v4306)))
(let ((e4312 (ite (bvsgt ((_ zero_extend 12) e4311) e4308)(_ bv1 1) (_ bv0 1))))
(let ((e4313 (ite (bvuge e4308 ((_ sign_extend 15) e4312))(_ bv1 1) (_ bv0 1))))
(let ((e4314 (ite (bvult e4308 ((_ sign_extend 11) v4304))(_ bv1 1) (_ bv0 1))))
(let ((e4315 (store a4307 ((_ sign_extend 9) e4314) ((_ zero_extend 6) v4304))))
(let ((e4316 (store a4307 ((_ sign_extend 9) e4313) ((_ extract 14 4) e4309))))
(let ((e4317 (select e4316 ((_ sign_extend 7) v4305))))
(let ((e4318 (store e4316 ((_ zero_extend 7) v4305) ((_ sign_extend 10) e4310))))
(let ((e4319 (ite (distinct ((_ zero_extend 1) v4305) e4311)(_ bv1 1) (_ bv0 1))))
(let ((e4320 ((_ zero_extend 7) v4303)))
(let ((e4321 (bvnand ((_ zero_extend 12) e4311) e4309)))
(let ((e4322 (bvor e4308 ((_ sign_extend 13) v4305))))
(let ((e4323 ((_ repeat 6) e4310)))
(let ((e4324 (ite (bvsle e4313 e4313)(_ bv1 1) (_ bv0 1))))
(let ((e4325 ((_ repeat 2) v4304)))
(let ((e4326 (bvmul ((_ zero_extend 15) e4312) e4322)))
(let ((e4327 (bvxor ((_ sign_extend 2) e4324) v4305)))
(let ((e4328 (bvsrem ((_ sign_extend 12) v4306) e4326)))
(let ((e4329 (bvlshr e4317 ((_ sign_extend 10) e4314))))
(let ((e4330 (bvslt ((_ zero_extend 13) v4305) e4309)))
(let ((e4331 (bvult v4303 v4303)))
(let ((e4332 (bvsge v4303 ((_ zero_extend 3) e4327))))
(let ((e4333 (bvuge e4323 ((_ sign_extend 3) e4327))))
(let ((e4334 (bvule e4328 ((_ zero_extend 12) e4311))))
(let ((e4335 (bvule ((_ zero_extend 15) e4319) e4321)))
(let ((e4336 (bvsgt e4320 ((_ zero_extend 10) e4327))))
(let ((e4337 (bvule e4325 ((_ zero_extend 4) v4303))))
(let ((e4338 (bvule ((_ sign_extend 10) e4310) e4317)))
(let ((e4339 (bvsge v4305 ((_ sign_extend 2) e4319))))
(let ((e4340 (bvsle v4305 ((_ zero_extend 2) e4313))))
(let ((e4341 (bvule e4326 ((_ zero_extend 5) e4329))))
(let ((e4342 (bvugt ((_ zero_extend 3) e4319) v4306)))
(let ((e4343 (bvsge ((_ zero_extend 9) e4311) e4320)))
(let ((e4344 (bvslt ((_ zero_extend 2) e4313) v4305)))
(let ((e4345 (bvugt ((_ sign_extend 5) e4317) e4308)))
(let ((e4346 (bvsle ((_ sign_extend 6) e4325) e4321)))
(let ((e4347 (bvugt e4310 e4319)))
(let ((e4348 (bvule ((_ zero_extend 2) e4313) e4327)))
(let ((e4349 (bvslt ((_ zero_extend 2) v4306) e4323)))
(let ((e4350 (= e4329 ((_ zero_extend 10) e4324))))
(let ((e4351 (bvsgt ((_ sign_extend 15) e4313) e4308)))
(let ((e4352 (bvsgt e4325 ((_ sign_extend 6) e4311))))
(let ((e4353 (bvuge e4325 ((_ zero_extend 9) e4319))))
(let ((e4354 (bvugt e4326 ((_ zero_extend 15) e4312))))
(let ((e4355 (bvsge e4313 e4319)))
(let ((e4356 (bvule v4304 v4304)))
(let ((e4357 (bvult e4321 ((_ zero_extend 10) v4303))))
(let ((e4358 (bvsge ((_ sign_extend 12) v4306) e4328)))
(let ((e4359 (bvugt ((_ sign_extend 12) e4312) e4320)))
(let ((e4360 (bvsge ((_ sign_extend 15) e4314) e4328)))
(let ((e4361 (distinct e4329 ((_ zero_extend 10) e4313))))
(let ((e4362 (bvugt ((_ zero_extend 12) e4313) e4320)))
(let ((e4363 (bvule e4326 ((_ zero_extend 12) e4311))))
(let ((e4364 (bvule ((_ sign_extend 10) e4323) e4321)))
(let ((e4365 (distinct e4308 ((_ sign_extend 6) e4325))))
(let ((e4366 (bvsge e4322 ((_ sign_extend 13) v4305))))
(let ((e4367 (= e4336 e4338)))
(let ((e4368 (or e4366 e4344)))
(let ((e4369 (=> e4355 e4368)))
(let ((e4370 (not e4340)))
(let ((e4371 (or e4345 e4358)))
(let ((e4372 (xor e4356 e4363)))
(let ((e4373 (or e4365 e4367)))
(let ((e4374 (=> e4350 e4349)))
(let ((e4375 (=> e4373 e4333)))
(let ((e4376 (= e4359 e4375)))
(let ((e4377 (ite e4370 e4331 e4337)))
(let ((e4378 (not e4369)))
(let ((e4379 (xor e4348 e4334)))
(let ((e4380 (and e4372 e4374)))
(let ((e4381 (=> e4379 e4362)))
(let ((e4382 (and e4361 e4376)))
(let ((e4383 (and e4378 e4354)))
(let ((e4384 (ite e4383 e4364 e4380)))
(let ((e4385 (=> e4360 e4343)))
(let ((e4386 (=> e4377 e4347)))
(let ((e4387 (=> e4341 e4342)))
(let ((e4388 (=> e4384 e4371)))
(let ((e4389 (and e4335 e4386)))
(let ((e4390 (ite e4382 e4339 e4352)))
(let ((e4391 (and e4390 e4332)))
(let ((e4392 (ite e4357 e4389 e4353)))
(let ((e4393 (or e4388 e4385)))
(let ((e4394 (xor e4346 e4391)))
(let ((e4395 (ite e4393 e4381 e4394)))
(let ((e4396 (xor e4351 e4387)))
(let ((e4397 (and e4392 e4392)))
(let ((e4398 (or e4330 e4396)))
(let ((e4399 (and e4395 e4397)))
(let ((e4400 (or e4399 e4398)))
(let ((e4401 (and e4400 (not (= e4326 (_ bv0 16))))))
(let ((e4402 (and e4401 (not (= e4326 (bvnot (_ bv0 16)))))))
(let ((e4403 (and e4402 (not (= v4306 (_ bv0 4))))))
e4403
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(pop 1)
