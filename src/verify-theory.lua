local profile = import "profile.lua"

local theory = {
	assertion_t = "Assertion",
	satisfaction_t = "any",
}

-- RETURNS a string
local function showAssertion(assertion)
	assertis(assertion, "Assertion")

	if assertion.tag == "unit" then
		return "(unit)"
	elseif assertion.tag == "this" then
		return "(this)"
	elseif assertion.tag == "variable" then
		return "(var " .. assertion.variable.name .. ")"
	elseif assertion.tag == "new-class" then
		local fields = {}
		for f, v in pairs(assertion.fields) do
			table.insert(fields, f .. "=" .. showAssertion(v))
		end
		table.sort(fields)
		fields = table.concat(fields, " ")
		return "(new-class " .. assertion.type .. " " .. fields .. ")"
	elseif assertion.tag == "static" then
		local arguments = {}
		for _, v in ipairs(assertion.arguments) do
			table.insert(arguments, showAssertion(v))
		end
		arguments = table.concat(arguments, " ")
		return "(method " .. assertion.staticName .. " " .. assertion.base .. " [" .. arguments .. "])"
	elseif assertion.tag == "method" then
		local arguments = {}
		for _, v in ipairs(assertion.arguments) do
			table.insert(arguments, showAssertion(v))
		end
		arguments = table.concat(arguments, " ")
		return "(method " .. assertion.methodName .. " " .. showAssertion(assertion.base) .. " [" .. arguments .. "])"
	elseif assertion.tag == "int" then
		return "(int " .. tostring(assertion.value) .. ")"
	elseif assertion.tag == "boolean" then
		return "(boolean " .. tostring(assertion.value) .. ")"
	end
	error("unknown assertion tag `" .. assertion.tag .. "` in showAssertion")
end
theory.showAssertion = showAssertion

function theory:isInconsistent(model)
	return false
end

local TERMINAL_TAG = {
	["unit"] = true,
	["this"] = true,
	["variable"] = true,
	["int"] = true,
	["boolean"] = true,
}

local function m_scan(self, object)
	assertis(object, "Assertion")

	local shown = showAssertion(object)
	if self.relevant[shown] then
		return self.relevant[shown]
	end

	local function ref(child)
		local s = showAssertion(child)
		assert(s ~= shown)
		assert(self.relevant[s], "child in map")
		self.referencedBy[child] = self.referencedBy[child] or {}
		table.insert(self.referencedBy[child], self.relevant[shown])
	end

	if TERMINAL_TAG[object.tag] then
		self.relevant[shown] = object
	elseif object.tag == "static" then
		local canon = freeze {
			tag = "static",
			base = object.base,
			staticName = object.staticName,
			arguments = table.map(table.bind(self, self.scan), object.arguments),
		}
		self.relevant[shown] = canon
		for _, argument in ipairs(canon.arguments) do
			ref(argument)
		end
	elseif object.tag == "method" then
		local canon = freeze {
			tag = "method",
			base = self:scan(object.base),
			methodName = object.methodName,
			arguments = table.map(table.bind(self, self.scan), object.arguments),
		}
		self.relevant[shown] = canon
		ref(canon.base)
		for _, argument in ipairs(canon) do
			ref(argument)
		end
	end

	assert(self.relevant[shown], "unhandled tag `" .. object.tag .. "`")
	return self.relevant[shown]
end

function theory:inModel(idSimple, targetAssertion, targetTruth)
	assertis(idSimple, mapType("Assertion", "boolean"))
	assertis(targetAssertion, "Assertion")
	assertis(targetTruth, "boolean")


	profile.open "canonicalization"
	-- 1) Generate a list of relevant subexpressions
	local canon = {scan = m_scan; relevant = {}, referencedBy = {}}

	local trueAssertion = canon:scan({tag = "boolean", value = true})
	local falseAssertion = canon:scan({tag = "boolean", value = false})

	targetAssertion = canon:scan(targetAssertion)

	local simple = {}
	for key, value in pairs(idSimple) do
		local object = canon:scan(key)
		
		-- After canonicalizing, two expressions with different truth
		-- assignments could be in the map
		if simple[object] and simple[object] ~= value then
			-- All truths are modeled by an inconsistent model
			profile.close()
			return true
		end
		simple[object] = value
	end
	assertis(simple, mapType("Assertion", "boolean"))
	assertis(canon.relevant, mapType("string", "Assertion"))
	assertis(canon.referencedBy, mapType("Assertion", listType("Assertion")))

	profile.close()

	profile.open "scan for equality"
	
	-- 2) Find all positive == assertions
	local positiveEq, negativeEq = {}, {}
	for assertion, truth in pairs(simple) do
		if assertion.tag == "method" and assertion.methodName == "eq" then
			assert(#assertion.arguments == 1)
			local left = canon:scan(assertion.base)
			local right = canon:scan(assertion.arguments[1])
			if truth then
				table.insert(positiveEq, {left, right})
			else
				table.insert(negativeEq, {left, right})
			end
		end
	end

	profile.close()

	-- 3) Use each positive == assertion to join representatives
	local representative = {}
	for _, expression in pairs(canon.relevant) do
		representative[expression] = expression
	end
	assertis(representative, mapType("Assertion", "Assertion"))

	-- RETURNS an Assertion that is equal to canonicalized assertion `of`
	local function rootRepresentative(of)
		assertis(of, "Assertion")
		
		-- REQUIRES that identities have already been canonicalized
		local parent = representative[of]
		assert(parent ~= nil)
		if parent == of then
			return parent
		end
		local root = rootRepresentative(parent)
		representative[of] = root
		return root
	end

	-- RETURNS true when assertions x, y are equivalent in the UF data structure
	local function areEqual(x, y)
		assertis(x, "Assertion")
		assertis(y, "Assertion")
		return rootRepresentative(x) == rootRepresentative(y)
	end

	local byStructure = {}
	-- RETURNS a string such that for x, y
	-- if approximateStructure(x) ~= approximateStructure(y)
	-- then x, y have different structure and thus childrenSame(x, y) is false
	local function approximateStructure(x)
		assertis(x, "Assertion")
		if x.tag == "method" then
			return "method-" .. x.methodName
		elseif x.tag == "static" then
			return "static-" .. x.staticName
		else
			return x.tag
		end
	end
	for _, x in pairs(canon.relevant) do
		local s = approximateStructure(x)
		byStructure[s] = byStructure[s] or {}
		table.insert(byStructure[s], x)
	end
	
	-- RETURNS true when assertions x, y are equivalent due to being
	-- equal functions of equal arguments 
	local function childrenSame(x, y)
		assertis(x, "Assertion")
		assertis(y, "Assertion")
		assert(not areEqual(x, y))

		if x.tag ~= y.tag then
			-- Elements that are structurally different cannot be shown
			-- to be the same here
			return false
		elseif TERMINAL_TAG[x.tag] then
			-- Terminal elements that aren't in the same representative group
			-- cannot be shown to be equal here
			return false
		elseif x.tag == "method" then
			if x.methodName ~= y.methodName then
				return false
			elseif not areEqual(x.base, y.base) then
				return false
			end
			assert(#x.arguments == #y.arguments)
			for i in ipairs(x.arguments) do
				if not areEqual(x.arguments[i], y.arguments[i]) then
					return false
				end
			end
			return true
		elseif x.tag == "static" then
			if x.staticName ~= y.staticName then
				return false
			end
			-- TODO
		end
		error("TODO childrenSame for tag `" .. x.tag .. "`")
	end

	-- RETURNS nothing
	local function union(a, b)
		assertis(a, "Assertion")
		assertis(b, "Assertion")

		local rootA = rootRepresentative(a)
		local rootB = rootRepresentative(b)
		if rootA ~= rootB then
			if math.random(2) == 1 then
				representative[rootA] = rootB
			else
				representative[rootB] = rootA
			end

			profile.open("recursive union")

			-- Union all functions of equal value

			-- TODO: need only consider `x`s that are reference a or b
			for _, x in pairs(canon.relevant) do
				local group = byStructure[approximateStructure(x)]
				local rootX = rootRepresentative(x)
				for _, y in ipairs(group) do
					local rootY = rootRepresentative(y)
					if rootX ~= rootY then
						assert(not areEqual(x, y))
						if childrenSame(x, y) then
							profile.open("sub fun eq")
							union(x, y)
							profile.close()
						end
						
						-- union() may modify the root representative of x,
						-- making `rootX` stale
						rootX = rootRepresentative(x)
					end
				end
			end

			profile.close("recursive union")
		end
	end

	profile.open "union-find"
	-- Union find
	for i, eq in ipairs(positiveEq) do
		profile.open("union-find " .. i .. "/" .. #positiveEq)
		union(eq[1], eq[2])
		profile.close()
	end
	profile.close()

	profile.open "negative =="
	-- 4) Use each negative == assertion to separate groups
	local negated = {}
	for _, eq in ipairs(negativeEq) do
		local a, b = eq[1], eq[2]
		local rootA = rootRepresentative(a)
		local rootB = rootRepresentative(b)

		if rootA == rootB then
			-- TODO: Inconsistent model
			print("INCONSISTENT!")
			profile.close()
			return true
		end
		negated[rootA] = negated[rootA] or {}
		negated[rootA][rootB] = true
		negated[rootB] = negated[rootB] or {}
		negated[rootB][rootA] = true
	end
	assertis(negated, mapType(
		self.assertion_t,
		mapType(self.assertion_t, constantType(true))
	))
	profile.close()

	-- RETURNS whether or not it is immediate that `assertion` has truth value
	-- `truth` in the given model after applying UF for equality
	local function immediately(assertion, truth)
		assertis(truth, "boolean")
		assert(rootRepresentative(assertion))
		--print("", "??", showAssertion(assertion), "=>?", truth)

		-- The boolean literals have known truth assignments
		if truth then
			if areEqual(assertion, trueAssertion) then
				return true
			end
		else
			if areEqual(assertion, falseAssertion) then
				return true
			end
		end
		
		for given, t in pairs(simple) do
			assert(rootRepresentative(given))
			local eq = areEqual(given, assertion)
			--print("", "", eq, "?=", showAssertion(given))
			if t == truth and eq then
				return true
			end
		end

		if assertion.tag == "method" and assertion.methodName == "eq" then
			assert(#assertion.arguments == 1)
			local left = rootRepresentative(assertion.base)
			local right = rootRepresentative(assertion.arguments[1])
			if truth then
				return areEqual(left, right)
			else
				return negated[left] and negated[left][right]
			end
		end
		return false
	end

	profile.open("immediately?")
	-- 5) Check if the assertion is true
	-- It may be equal to any true statement
	for _, r in pairs(canon.relevant) do
		if areEqual(r, targetAssertion) then
			--print()
			--print("", "@", showAssertion(r))
			local holds = immediately(r, targetTruth)
			--print("", "", holds)
			if holds then
				profile.close()
				return true
			end
		end
	end

	profile.close()

	--print("{")
	--for key, value in pairs(idSimple) do
	--	print("", showAssertion(key), "=>", value)
	--end
	--print("}")

	--print("don't know how to prove", show(targetAssertion):gsub("%s+", " "), "")
	return false
end

function theory:breakup(assertion, target)
	assertis(assertion, "Assertion")

	if assertion.tag == "method" then
		if assertion.methodName == "and" then
			if target == true then
				local truths = {{true, true}}
				return {assertion.base, assertion.arguments[1]}, truths
			else
				local truths = {{false, false}, {false, true}, {true, false}}
				return {assertion.base, assertion.arguments[1]}, truths
			end
		elseif assertion.methodName == "not" then
			if target == true then
				local truths = {{false}}
				return {assertion.base}, truths
			else
				local truths = {{true}}
				return {assertion.base}, truths
			end
		end
	end

	return false
end

return theory
